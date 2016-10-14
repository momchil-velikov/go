// Copyright 2015 The Go Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

package ssa

import (
	"fmt"
	"sort"
)

func dumpPartitions(f *Func, partition []eqclass, kind string) {
	for i, e := range partition {
		if len(e) > 500 {
			fmt.Printf("FN: %s CSE.%s.large partition (%d): ", f.Name, kind, len(e))
			for j := 0; j < 3; j++ {
				fmt.Printf("%s ", e[j].LongString())
			}
			fmt.Println()
		}
		if len(e) > 1 {
			fmt.Printf("FN: %s CSE.%s.partition #%d:", f.Name, kind, i)
			for _, v := range e {
				fmt.Printf(" %s", v.String())
			}
			fmt.Printf("\n")
		}
	}
}

// cse does common-subexpression elimination on the Function.
// Values are just relinked, nothing is deleted. A subsequent deadcode
// pass is required to actually remove duplicate expressions.
func cse(f *Func) {
	// Two values are equivalent if they satisfy the following definition:
	// equivalent(v, w):
	//   v.op == w.op
	//   v.type == w.type
	//   v.aux == w.aux
	//   v.auxint == w.auxint
	//   len(v.args) == len(w.args)
	//   v.block == w.block if v.op == OpPhi
	//   equivalent(v.args[i], w.args[i]) for i in 0..len(v.args)-1

	// The algorithm searches for a partition of f's values into
	// equivalence classes using the above definition.
	// It starts with a coarse partition and iteratively refines it
	// until it reaches a fixed point.

	// Make initial coarse partitions by using a subset of the conditions above.
	a := make([]*Value, 0, f.NumValues())
	auxIDs := auxmap{}
	for _, b := range f.Blocks {
		for _, v := range b.Values {
			if auxIDs[v.Aux] == 0 {
				auxIDs[v.Aux] = int32(len(auxIDs)) + 1
			}
			if v.Type.IsMemory() {
				continue // memory values can never cse
			}
			if opcodeTable[v.Op].commutative && len(v.Args) == 2 && v.Args[1].ID < v.Args[0].ID {
				// Order the arguments of binary commutative operations.
				v.Args[0], v.Args[1] = v.Args[1], v.Args[0]
			}
			a = append(a, v)
		}
	}
	partition := partitionValues(a, auxIDs)

	if f.pass.debug > 2 {
		dumpPartitions(f, partition, "INITIAL")
	}

	// map from value id back to eqclass id
	valueEqClass := make(map[ID]ID, f.NumValues())
	for _, b := range f.Blocks {
		for _, v := range b.Values {
			// Use negative equivalence class #s for unique values.
			valueEqClass[v.ID] = -v.ID
		}
	}
	var pNum ID = 0
	for _, e := range partition {
		for _, v := range e {
			valueEqClass[v.ID] = pNum
		}
		pNum++
	}

	// Split equivalence classes at points where they have
	// non-equivalent arguments.  Repeat until we can't find any
	// more splits.
	var splitPoints []int
	for {
		changed := false

		// partition can grow in the loop. By not using a range loop here,
		// we process new additions as they arrive, avoiding O(n^2) behavior.
		for i := 0; i < len(partition); i++ {
			e := partition[i]

			// Sort by eq class of arguments.
			sort.Sort(partitionByArgClass{e, valueEqClass})

			// Find split points.
			splitPoints = append(splitPoints[:0], 0)
			for j := 1; j < len(e); j++ {
				v, w := e[j-1], e[j]
				eqArgs := true
				for k, a := range v.Args {
					b := w.Args[k]
					if valueEqClass[a.ID] != valueEqClass[b.ID] {
						eqArgs = false
						break
					}
				}
				if !eqArgs {
					splitPoints = append(splitPoints, j)
				}
			}
			if len(splitPoints) == 1 {
				continue // no splits, leave equivalence class alone.
			}

			partition[i] = e[splitPoints[0]:splitPoints[1]]
			if len(partition[i]) == 1 {
				v := partition[i][0]
				valueEqClass[v.ID] = -v.ID
			}
			i--

			// Add new equivalence classes for the parts of e we found.
			splitPoints = append(splitPoints, len(e))
			for j := 1; j < len(splitPoints)-1; j++ {
				f := e[splitPoints[j]:splitPoints[j+1]]
				if len(f) == 1 {
					// Don't add singletons.
					valueEqClass[f[0].ID] = -f[0].ID
					continue
				}
				for _, v := range f {
					valueEqClass[v.ID] = pNum
				}
				pNum++
				partition = append(partition, f)
			}
			changed = true
		}

		if !changed {
			break
		}
	}

	if f.pass.debug > 2 {
		dumpPartitions(f, partition, "EQCLASS")
	}

	sdom := f.sdom()

	// Compute substitutions we would like to do. We substitute v for w
	// if v and w are in the same equivalence class and v dominates w.
	rewrite := make([]*Value, f.NumValues())
	for _, e := range partition {
		sort.Sort(partitionByDom{e, sdom})
		for i := 0; i < len(e)-1; i++ {
			// e is sorted by domorder, so a maximal dominant element is first in the slice
			v := e[i]
			if v == nil {
				continue
			}

			// Replace all elements of e which v dominates
			for j := i + 1; j < len(e); j++ {
				w := e[j]
				if w == nil {
					continue
				}
				if sdom.isAncestorEq(v.Block, w.Block) {
					rewrite[w.ID] = v
					e[j] = nil
				} else {
					// e is sorted by domorder, so v.Block doesn't dominate any subsequent blocks in e
					break
				}
			}
		}
	}

	// if we rewrite a tuple generator to a new one in a different block,
	// copy its selectors to the new generator's block, so tuple generator
	// and selectors stay together.
	// be careful not to copy same selectors more than once (issue 16741).
	copiedSelects := make(map[ID][]*Value)
	for _, b := range f.Blocks {
	out:
		for _, v := range b.Values {
			if rewrite[v.ID] != nil {
				continue
			}
			if v.Op != OpSelect0 && v.Op != OpSelect1 {
				continue
			}
			if !v.Args[0].Type.IsTuple() {
				f.Fatalf("arg of tuple selector %s is not a tuple: %s", v.String(), v.Args[0].LongString())
			}
			t := rewrite[v.Args[0].ID]
			if t != nil && t.Block != b {
				// v.Args[0] is tuple generator, CSE'd into a different block as t, v is left behind
				for _, c := range copiedSelects[t.ID] {
					if v.Op == c.Op {
						// an equivalent selector is already copied
						rewrite[v.ID] = c
						continue out
					}
				}
				c := v.copyInto(t.Block)
				rewrite[v.ID] = c
				copiedSelects[t.ID] = append(copiedSelects[t.ID], c)
			}
		}
	}

	rewrites := int64(0)

	// Apply substitutions
	for _, b := range f.Blocks {
		for _, v := range b.Values {
			for i, w := range v.Args {
				if x := rewrite[w.ID]; x != nil {
					v.SetArg(i, x)
					rewrites++
				}
			}
		}
		if v := b.Control; v != nil {
			if x := rewrite[v.ID]; x != nil {
				if v.Op == OpNilCheck {
					// nilcheck pass will remove the nil checks and log
					// them appropriately, so don't mess with them here.
					continue
				}
				b.SetControl(x)
			}
		}
	}

	// Hoist values.
	if f.pass.debug > 2 {
		dumpPartitions(f, partition, "AFTER")
	}

	hoists := hoistValues(f, partition, valueEqClass)
	if hoists > 0 {
		deadcode(f)
		phielim(f)
	}

	if f.pass.stats > 0 {
		f.LogStat("CSE HOISTED", hoists)
	}

	if f.pass.stats > 0 {
		f.LogStat("CSE REWRITES", rewrites)
	}
}

// An eqclass approximates an equivalence class. During the
// algorithm it may represent the union of several of the
// final equivalence classes.
type eqclass []*Value

// partitionValues partitions the values into equivalence classes
// based on having all the following features match:
//  - opcode
//  - type
//  - auxint
//  - aux
//  - nargs
//  - block # if a phi op
//  - first two arg's opcodes and auxint
//  - NOT first two arg's aux; that can break CSE.
// partitionValues returns a list of equivalence classes, each
// being a sorted by ID list of *Values. The eqclass slices are
// backed by the same storage as the input slice.
// Equivalence classes of size 1 are ignored.
func partitionValues(a []*Value, auxIDs auxmap) []eqclass {
	sort.Sort(sortvalues{a, auxIDs})

	var partition []eqclass
	for len(a) > 0 {
		v := a[0]
		j := 1
		for ; j < len(a); j++ {
			w := a[j]
			if cmpVal(v, w, auxIDs) != CMPeq {
				break
			}
		}
		if j > 1 {
			partition = append(partition, a[:j])
		}
		a = a[j:]
	}

	return partition
}
func lt2Cmp(isLt bool) Cmp {
	if isLt {
		return CMPlt
	}
	return CMPgt
}

type auxmap map[interface{}]int32

func cmpVal(v, w *Value, auxIDs auxmap) Cmp {
	// Try to order these comparison by cost (cheaper first)
	if v.Op != w.Op {
		return lt2Cmp(v.Op < w.Op)
	}
	if v.AuxInt != w.AuxInt {
		return lt2Cmp(v.AuxInt < w.AuxInt)
	}
	if len(v.Args) != len(w.Args) {
		return lt2Cmp(len(v.Args) < len(w.Args))
	}
	if v.Op == OpPhi && v.Block != w.Block {
		return lt2Cmp(v.Block.ID < w.Block.ID)
	}
	if v.Type.IsMemory() {
		// We will never be able to CSE two values
		// that generate memory.
		return lt2Cmp(v.ID < w.ID)
	}

	if tc := v.Type.Compare(w.Type); tc != CMPeq {
		return tc
	}

	if v.Aux != w.Aux {
		if v.Aux == nil {
			return CMPlt
		}
		if w.Aux == nil {
			return CMPgt
		}
		return lt2Cmp(auxIDs[v.Aux] < auxIDs[w.Aux])
	}

	return CMPeq
}

// Sort values to make the initial partition.
type sortvalues struct {
	a      []*Value // array of values
	auxIDs auxmap   // aux -> aux ID map
}

func (sv sortvalues) Len() int      { return len(sv.a) }
func (sv sortvalues) Swap(i, j int) { sv.a[i], sv.a[j] = sv.a[j], sv.a[i] }
func (sv sortvalues) Less(i, j int) bool {
	v := sv.a[i]
	w := sv.a[j]
	if cmp := cmpVal(v, w, sv.auxIDs); cmp != CMPeq {
		return cmp == CMPlt
	}

	// Sort by value ID last to keep the sort result deterministic.
	return v.ID < w.ID
}

type partitionByDom struct {
	a    []*Value // array of values
	sdom SparseTree
}

func (sv partitionByDom) Len() int      { return len(sv.a) }
func (sv partitionByDom) Swap(i, j int) { sv.a[i], sv.a[j] = sv.a[j], sv.a[i] }
func (sv partitionByDom) Less(i, j int) bool {
	v := sv.a[i]
	w := sv.a[j]
	return sv.sdom.domorder(v.Block) < sv.sdom.domorder(w.Block)
}

type partitionByArgClass struct {
	a       []*Value  // array of values
	eqClass map[ID]ID // equivalence class IDs of values
}

func (sv partitionByArgClass) Len() int      { return len(sv.a) }
func (sv partitionByArgClass) Swap(i, j int) { sv.a[i], sv.a[j] = sv.a[j], sv.a[i] }
func (sv partitionByArgClass) Less(i, j int) bool {
	v := sv.a[i]
	w := sv.a[j]
	for i, a := range v.Args {
		b := w.Args[i]
		if sv.eqClass[a.ID] < sv.eqClass[b.ID] {
			return true
		}
		if sv.eqClass[a.ID] > sv.eqClass[b.ID] {
			return false
		}
	}
	return false
}

type hoistDst struct {
	blk *Block
	v   *Value
	vs  []*Value
}

type hoistState struct {
	fn           *Func
	partition    []eqclass
	valueEqClass map[ID]ID
	antOut       []*sparseSet
	done         map[ID]struct{}
}

func addHoistCandidate(f *Func, ds []hoistDst, b *Block) []hoistDst {
	// Do not add the block, if it's dominated by an existing block.
	for i := range ds {
		if f.sdom().isAncestorEq(ds[i].blk, b) {
			return ds
		}
	}
	// Remove the blocks, dominated by the new block.
	i := 0
	for i < len(ds) {
		if f.sdom().isAncestor(b, ds[i].blk) {
			ds[i].blk = ds[len(ds)-1].blk
			ds = ds[:len(ds)-1]
			continue
		}
		i++
	}
	return append(ds, hoistDst{blk: b})
}

func canHoistValue(v *Value) bool {
	// Do not hoist PHIs, as the new block can have different
	// predecessor count.
	if v.Op == OpPhi {
		return false
	}
	// Don't hoist tuples for now, as they must drag along their
	// selects. TODO: hoist tuples.
	if v.Type.IsTuple() {
		return false
	}
	// Do not hoist memory modifying operations.
	if v.Type.IsMemory() {
		return false
	}
	// Do not hoist control values. They are always live and the
	// compiler may put the original value back, in effect increasing
	// code size and execution time.
	if v == v.Block.Control {
		return false
	}
	return true
}

// hoistPlan finds a set of hoist destination blocks for an equivalence
// class and distributes the values to the hoist destinations.
func (s *hoistState) hoistPlan(classID ID) []hoistDst {
	// Collect hoist candidate blocks.  NOTE: here's the place to
	// implement or experiment with various strategies for choosing
	// hoist destinations.
	var ds []hoistDst
	// idom := s.fn.idom()
	for _, v := range s.partition[classID] {
		if len(v.Block.Preds) != 1 {
			continue
		}
		d := v.Block.Preds[0].b
		if s.antOut[d.ID].contains(classID) {
			ds = addHoistCandidate(s.fn, ds, d)
		}
		// d := idom[v.Block.ID]
		// if d != nil && s.antOut[d.ID].contains(classID) {
		// 	ds = addHoistCandidate(s.fn, ds, d)
		// }
	}
	if len(ds) == 0 {
		return nil
	}
	// Distribute values to hoist candidate blocks.
	sdom := s.fn.sdom()
	for _, v := range s.partition[classID] {
		if v == nil {
			continue
		}
		for i := range ds {
			b := ds[i].blk
			if sdom.isAncestor(b, v.Block) {
				ds[i].vs = append(ds[i].vs, v)
				break
			}
		}
	}
	return ds
}

// anticipatedExprs computes at each block exit the set of expressions,
// evaluated on each path, which starts from the point after the block.
// Each expression is represented by the equivalence class ID of the
// expression's Value. Unlike the classical anticipated/very busy
// expressions analysis, we are not concerned with the availability of
// the operands at this point as the availability may change as a result
// of our own transformations.
func anticipatedExprs(f *Func, partition []eqclass, valueEqClass map[ID]ID) []*sparseSet {
	// Map from block IDs to sets of anticipated expressions.
	antOut := make([]*sparseSet, f.NumBlocks())
	antIn := make([]*sparseSet, f.NumBlocks())
	nEqClass := len(partition)
	for i := range antOut {
		antIn[i] = newSparseSet(nEqClass)
		antOut[i] = newSparseSet(nEqClass)
	}
	// Temporary buffer for removing elements from a set.
	post := postorder(f)
	for {
		change := false
		// It's a backward dataflow analysis, hence traverse the blocks
		// in postorder.
		for _, b := range post {
			// fmt.Println("DBG: begin block", b)
			// Evaluate antOut for the current block as the
			// intersection of antIn's of the successor blocks.
			if len(b.Succs) == 0 {
				antOut[b.ID].clear()
			} else {
				antOut[b.ID].set(antIn[b.Succs[0].b.ID])
				for i := 1; i < len(b.Succs); i++ {
					antOut[b.ID].intersect(antIn[b.Succs[i].b.ID])
				}
			}
			// Copy antOut and propagate it backwards to the beginning
			// of the block, where it will become the antIn for the
			// block.
			s := new(sparseSet).set(antOut[b.ID])
			// Add all the expressions, computed in the block, to the
			// set, except the ones, which are alone in their
			// equivalence class, as we won't move them anyway.
			for _, v := range b.Values {
				if id := valueEqClass[v.ID]; id >= 0 && len(partition[id]) > 1 {
					s.add(id)
				}
			}

			if !s.equal(antIn[b.ID]) {
				antIn[b.ID].set(s)
				change = true
			}
		}
		if !change {
			break
		}
	}

	if f.pass.debug > 1 {
		fmt.Println("CSE anticipated expressions")
		for _, b := range post {
			if f.pass.debug > 2 {
				if antIn[b.ID].size() > 0 {
					fmt.Printf(" IN(b%d): [", b.ID)
					for _, id := range antIn[b.ID].contents() {
						rep := partition[id][0]
						fmt.Printf(" %s", rep)
					}
					fmt.Println(" ]")
				}
			}
			if antOut[b.ID].size() > 0 {
				fmt.Printf("OUT(b%d): [", b.ID)
				for _, id := range antOut[b.ID].contents() {
					rep := partition[id][0]
					fmt.Printf(" %s", rep)
				}
				fmt.Println(" ]")
			}
		}
	}

	return antOut
}

func availableOnExit(b *Block, v *Value) bool {
	return b.Func.sdom().isAncestorEq(v.Block, b)
}

func anyAvailableOnExit(b *Block, e eqclass) *Value {
	for _, v := range e {
		if availableOnExit(b, v) {
			return v
		}
	}
	return nil
}

// availableArgs replaces each element of `args` with a Value of the same
// equivalence class, which is available at the exit of `b`. If at least
// one argument is not available, the function return false.
func (s *hoistState) availableArgs(b *Block, args []*Value) bool {
	if b.Func.pass.debug > 3 {
		fmt.Println("DBG: checking operands", args)
		//fmt.Println("DBF: valueEqClass =", valueEqClass)
	}
	for i, a := range args {
		u := a
		// If the argument is a copy, use directly the copy
		// source. FIXME comment how this unblocks hoisting entire
		// dependency chains.
		if u.Op == OpCopy {
			u = u.Args[0]
		}
		id := s.valueEqClass[u.ID]
		if b.Func.pass.debug > 3 {
			fmt.Printf("DBG: check operand class #%d\n", id)
		}
		if id < 0 {
			if !availableOnExit(b, u) {
				if b.Func.pass.debug > 3 {
					fmt.Printf("DBG: %s not available at %s\n", u, b)
				}
				return false
			}
		} else if u = anyAvailableOnExit(b, s.partition[id]); u == nil {
			if b.Func.pass.debug > 3 {
				fmt.Println("DBG: none of", s.partition[id], "is available at", b)
			}
			return false
		}
		args[i] = u
	}
	return true
}

func (s *hoistState) hoistClass(classID ID) int64 {
	if len(s.partition[classID]) < 2 {
		return 0
	}
	if _, ok := s.done[classID]; ok {
		return 0
	}
	s.done[classID] = struct{}{}

	if s.fn.pass.debug > 3 {
		fmt.Printf("DBG: hoist class #%d\n", classID)
	}
	hoists := int64(0)
	// For each value in the partition attempt to hoist its operands
	// first.
	for _, v := range s.partition[classID] {
		for _, a := range v.Args {
			id := s.valueEqClass[a.ID]
			if id < 0 {
				continue
			}
			hoists += s.hoistClass(id)
		}
	}
	dst := s.hoistPlan(classID)
	if s.fn.pass.debug > 3 {
		fmt.Printf("DBG: plan for #%d\n", classID)
		for i := range dst {
			fmt.Printf("DBG: %s <-", dst[i].blk)
			for _, v := range dst[i].vs {
				fmt.Print(" ", v)
			}
			fmt.Println()
		}
	}
	for i := range dst {
		if len(dst[i].vs) < 2 {
			continue
		}
		b := dst[i].blk
		v := dst[i].vs[0]

		// Make sure the hoisted expression operands are available at
		// the hoist destination by considering each member of the
		// operand's equivalence class and picking up an available one.
		var tmp [3]*Value
		args := tmp[:0]
		args = append(args, v.Args...)
		if !s.availableArgs(b, args) {
			if s.fn.pass.debug > 3 {
				fmt.Printf("DBG: %v operands not available at %s\n", v, b)
			}
			continue
		}
		// Add a new value to the destination block. It belongs to the
		// same equivalence class as the one we are hoisting now.
		c := b.NewValue0(v.Line, v.Op, v.Type)
		c.Aux = v.Aux
		c.AuxInt = v.AuxInt
		c.AddArgs(args...)
		s.valueEqClass[c.ID] = classID
		dst[i].v = c
		if s.fn.pass.debug > 1 {
			fmt.Printf("FN: %s CSE.HOIST: %s <-", s.fn.Name, b)
			for _, u := range dst[i].vs {
				fmt.Print(" ", u)
			}
			fmt.Println()
		}
		// Replace the hoisted values with copy ops.
		for _, u := range dst[i].vs {
			if u.Type.IsVoid() {
				u.reset(OpInvalid)
			} else {
				u.reset(OpCopy)
				u.AddArg(c)
			}
		}
		// Mark the equivalence class as hoisted.
		hoists += int64(len(dst[i].vs))
	}
	// Leave in the class only the new instructions.
	n := 0
	for i := range dst {
		if v := dst[i].v; v != nil {
			s.partition[classID][n] = v
			n++
		}
	}
	s.partition[classID] = s.partition[classID][:n]
	if s.fn.pass.debug > 3 {
		fmt.Printf("DBG: done class #%d\n", classID)
	}
	return hoists
}

func hoistValues(f *Func, partition []eqclass, valueEqClass map[ID]ID) int64 {
	// Collect hoist candidate values at the beginning of the parition.
	// There should be at least two left in the equivalence class after
	// the CSE to consider hoisting them.
	n := 0
	for i, e := range partition {
		k := 0
		for _, v := range e {
			if v != nil && canHoistValue(v) {
				e[k] = v
				k++
			}
		}
		e = e[:k]
		if k >= 2 {
			n += k
		}
		partition[i] = e
	}
	if n == 0 {
		return 0
	}

	s := hoistState{
		fn:           f,
		partition:    partition,
		valueEqClass: valueEqClass,
		antOut:       anticipatedExprs(f, partition, valueEqClass),
		done:         make(map[ID]struct{}),
	}

	hoists := int64(0)
	for i := range partition {
		hoists += s.hoistClass(ID(i))
	}
	return hoists
}
