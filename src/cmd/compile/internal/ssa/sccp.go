package ssa

import (
	"fmt"
	"math"
)

// Sparse Conditonal Constant Propagation pass, based on:

// Mark N. Wegman and F. Kenneth Zadeck. 1991. Constant propagation with conditional branches.
// ACM Trans. Program. Lang. Syst. 13, 2 (April 1991), 181-210.
// DOI=http://dx.doi.org/10.1145/103135.103136

type latticeKind int

const (
	latticeTop latticeKind = iota
	latticeConst
	latticeBottom
)

func (k latticeKind) String() string {
	switch k {
	case latticeTop:
		return "TOP"
	case latticeConst:
		return "CONST"
	case latticeBottom:
		return "BOTTOM"
	default:
		panic("not reached")
	}
}

type latticeValue struct {
	kind latticeKind
	bits int64
}

func (lv latticeValue) String() string {
	return fmt.Sprintf("{%s, %d}", lv.kind, lv.bits)
}

type latticeCell struct {
	v   *Value
	lv  latticeValue
	use []*Value
	ctl []*Block
}

type sccpState struct {
	f        *Func
	cells    []latticeCell
	exec     map[Edge]bool
	flowlist []Edge
	ssalist  *sparseSet
}

func sccp(f *Func) {
	if f.pass.debug > 1 {
		fmt.Printf("SCCP func %s:\n", f.Name)
	}

	s := sccpState{
		f:       f,
		cells:   make([]latticeCell, f.NumValues()),
		exec:    make(map[Edge]bool),
		ssalist: newSparseSet(f.NumValues()),
	}

	// Collect all uses of each value and all blocks, where a value is
	// the control value.
	for _, b := range f.Blocks {
		for _, v := range b.Values {
			s.cells[v.ID].v = v
			for _, a := range v.Args {
				s.cells[a.ID].use = append(s.cells[a.ID].use, v)
			}
		}
		if v := b.Control; v != nil {
			s.cells[v.ID].ctl = append(s.cells[v.ID].ctl, b)
		}
	}

	// Start by visiting the entry basic block and loop until there is
	// no more work in the two work lists.
	s.visitExprs(f.Entry)
	for len(s.flowlist) > 0 || s.ssalist.size() > 0 {
		switch {
		case len(s.flowlist) > 0:
			// Fetch a control-flow edge from the "flow" worklist.
			e := s.flowlist[len(s.flowlist)-1]
			s.flowlist = s.flowlist[:len(s.flowlist)-1]

			// If edge was already marked as executable, do not enter
			// the block a second time.
			if s.exec[e] {
				continue
			}
			s.exec[e] = true

			// Find which incoming edges are marked as executable.
			tmp := [4]bool{}
			x, n := s.execEdges(e.b, tmp[:0])

			// Visit φ-ops, as their value potentially changes with each
			// new executable edge.
			s.visitPhis(e.b.Preds[e.i].b, e.b, x)

			// The non-φ ops are as a whole only once, following the first
			// executable edge into the block.
			if n > 1 {
				continue
			}
			s.visitExprs(e.b)

		case s.ssalist.size() > 0:
			// Fetch an SSA edge from the SSA worklist (SSA edges are
			// represented only with their heads).
			v := s.cells[s.ssalist.pop()].v

			// For the block, containing the value, lFind which incoming
			// edges are marked as executable.
			tmp := [4]bool{}
			x, n := s.execEdges(v.Block, tmp[:0])

			// Visit φ-ops always, but non-φ ops only if there is at
			// least one executable edge into the block.
			if v.Op == OpPhi {
				s.visitPhi(v, x)
			} else if n > 0 {
				s.visitExpr(v)
			}
		}
	}

	if f.pass.debug > 2 {
		for i := range s.cells {
			v := s.cells[i].v
			if v == nil || isConst(v.Op) {
				continue
			}
			if s.cells[i].lv.kind != latticeConst && f.pass.debug <= 2 {
				continue
			}
			fmt.Printf("SCCP %s, %s\n", s.cells[i].lv, v.LongString())
		}
	}

	// Replace operations with the corresponing constants.
	for i := range s.cells {
		v := s.cells[i].v
		if v == nil || isConst(v.Op) {
			continue
		}
		lv := s.cells[i].lv
		if lv.kind != latticeConst {
			continue
		}
		if f.pass.debug > 1 {
			fmt.Printf("SCCP: rewrite %s", v.LongString())
		}
		switch {
		case v.Type.IsBoolean():
			v.reset(OpConstBool)
		case v.Type.IsInteger():
			switch v.Type.Size() {
			case 1:
				v.reset(OpConst8)
			case 2:
				v.reset(OpConst16)
			case 4:
				v.reset(OpConst32)
			case 8:
				v.reset(OpConst64)
			default:
				panic("not reached")
			}
		case v.Type.IsFloat():
			if v.Type.Size() == 4 {
				v.reset(OpConst32F)
			} else if v.Type.Size() == 8 {
				v.reset(OpConst64F)
			} else {
				panic("not reached")
			}
		default:
			panic("not reached")
		}
		v.AuxInt = lv.bits
		if f.pass.debug > 1 {
			fmt.Printf(" to %s\n", v.LongString())
		}
	}
}

// execEdges returns a slice with i-th element set to true iff the i-th
// incoming edge to a block is marked executable. It also returns the
// total number of true elements in the slice.
func (s *sccpState) execEdges(b *Block, x []bool) ([]bool, int) {
	n := 0
	for i := range b.Preds {
		p, j := b.Preds[i].b, b.Preds[i].i
		x = append(x, s.exec[p.Succs[j]])
		if x[len(x)-1] {
			n++
		}
	}
	return x, n
}

// visitPhi visits all the φ-ops in the block `b`. The slice `x` marks
// each executable predecessor edge of the block.
func (s *sccpState) visitPhis(p *Block, b *Block, x []bool) {
	if s.f.pass.debug > 2 {
		fmt.Printf("SCCP enter phis %s -> %s\n", p, b)
		defer fmt.Printf("SCCP exit phis %s\n", b)
	}

	for _, v := range b.Values {
		if v.Op == OpPhi {
			s.visitPhi(v, x)
		}
	}
}

// visitPhi computes the lattice value of the φ-op `v`. The φ arguments,
// which correspond to non-executable edges (as indicated by the `x`
// slice) are considered to have value TOP.
func (s *sccpState) visitPhi(v *Value, x []bool) {
	new := latticeValue{}
	for i := 0; i < len(v.Args) && new.kind != latticeBottom; i++ {
		if !x[i] {
			continue
		}
		av := s.cells[v.Args[i].ID].lv
		switch av.kind {
		case latticeTop:
			continue
		case latticeBottom:
			new.kind = latticeBottom
		default:
			if new.kind == latticeTop {
				new = av
			} else if new.bits != av.bits {
				new.kind = latticeBottom
			}
		}
	}

	old := s.cells[v.ID].lv
	s.cells[v.ID].lv = new

	if s.f.pass.debug > 2 {
		fmt.Printf("SCCP PHI %s: old: %s, new: %s\n", v, old, new)
	}

	if old.kind != new.kind {
		s.propagate(v)
	}
}

// visitExprs visits all the non-φ in the block `b`. This is run only
// when the block is encounterest for teh first time followin an
// executable edge.
func (s *sccpState) visitExprs(b *Block) {
	if s.f.pass.debug > 2 {
		fmt.Printf("SCCP enter %s\n", b)
		defer fmt.Printf("SCCP exit %s\n", b)

	}
	for _, v := range b.Values {
		if v.Op == OpPhi {
			continue
		}
		s.visitExpr(v)
	}

	// If the block unconditionally transfers control to its successor,
	// add the outgoing edge to the flow worklist.
	if b.Kind == BlockPlain || b.Kind == BlockFirst {
		s.flowlist = append(s.flowlist, b.Succs[0])
	}
}

// visitExpr computes the lattice value of a non-φ operation.
func (s *sccpState) visitExpr(v *Value) {
	new := latticeValue{}
	if isConst(v.Op) {
		// OpConst* operations are trivially lattice constants.
		new = latticeValue{kind: latticeConst, bits: v.AuxInt}
	} else if t, ok := getFoldFn(v.Op); !ok {
		// If there is no fold function for this o, the latice value is
		// BOTTOM, not a constant.
		new.kind = latticeBottom
	} else {
		tmpKind := [2]latticeKind{}
		tmpArgs := [2]int64{}
		kinds := tmpKind[:0]
		args := tmpArgs[:0]
		ntop, nbot := 0, 0

		// Collect the lattice values, corresponding to the arguments.
		for _, u := range v.Args {
			a := s.cells[u.ID].lv
			kinds = append(kinds, a.kind)
			args = append(args, a.bits)
			if a.kind == latticeTop {
				ntop++
			} else if a.kind == latticeBottom {
				nbot++
			}
		}
		// Invoke the fold function. Fold functions are two kinds. For
		// the majority of the operations, if any argument is BOTTOM,
		// then the result is BOTTOM and if any argument is TOP, then
		// the result is TOP.  Some operations, however, can evaluate to
		// a constant even if some of the arguments are TOP or BOTTOM,
		// for example true || <any> == true.
		if t.genFn == nil {
			if nbot > 0 {
				new.kind = latticeBottom
			} else if ntop == 0 {
				new.kind = latticeConst
				new.bits = t.fn(args)
			}
		} else {
			new = t.genFn(kinds, args)
		}
	}

	old := s.cells[v.ID].lv
	s.cells[v.ID].lv = new

	if s.f.pass.debug > 2 {
		fmt.Printf("SCCP %s: old: %s, new: %s\n", v, old, new)
	}

	if old.kind != new.kind {
		s.propagate(v)
	}
}

// propagate adds items to the flow worklist or the SSA worklist after
// the lattice value of `v` has been lowered.
func (s *sccpState) propagate(v *Value) {
	// Propagate the change along SSA (data-flow) edges.
	for _, u := range s.cells[v.ID].use {
		s.ssalist.add(u.ID)
	}
	// Propagate the change along the control-flow edges.  If the
	// control value is not a constant (BOTTOM), the all the successor
	// edges are potentially executed. If the control value is a
	// constants, only the successor, corresponding to the value of the
	// constant (true or false) is potentially executed. The lattice
	// value of `v` has been lowered, hence it cannot be TOP.
	for _, b := range s.cells[v.ID].ctl {
		if lv := s.cells[v.ID].lv; lv.kind == latticeBottom {
			s.flowlist = append(s.flowlist, b.Succs...)
		} else if lv.bits == 0 {
			s.flowlist = append(s.flowlist, b.Succs[1])
		} else {
			s.flowlist = append(s.flowlist, b.Succs[0])
		}
	}
}

// Constat fold functions.
func i32f(x int64) float32 {
	return math.Float32frombits(uint32(x))
}

func i64f(x int64) float64 {
	return math.Float64frombits(uint64(x))
}

func f32i(x float32) int64 {
	return int64(math.Float32bits(x))
}

func f64i(x float64) int64 {
	return int64(math.Float64bits(x))
}

func foldAdd8(a []int64) int64 {
	return int64(int8(a[0] + a[1]))
}

func foldAdd16(a []int64) int64 {
	return int64(int16(a[0] + a[1]))
}

func foldAdd32(a []int64) int64 {
	return int64(int32(a[0] + a[1]))
}

func foldAdd64(a []int64) int64 {
	return a[0] + a[1]
}

func foldAdd32F(a []int64) int64 {
	return f32i(i32f(a[0]) + i32f(a[1]))
}

func foldAdd64F(a []int64) int64 {
	return f64i(i64f(a[0]) + i64f(a[1]))
}

func foldSub8(a []int64) int64 {
	return int64(int8(a[0] - a[1]))
}

func foldSub16(a []int64) int64 {
	return int64(int16(a[0] - a[1]))
}

func foldSub32(a []int64) int64 {
	return int64(int32(a[0] - a[1]))
}

func foldSub64(a []int64) int64 {
	return a[0] - a[1]
}

func foldSub32F(a []int64) int64 {
	return f32i(i32f(a[0]) - i32f(a[1]))
}

func foldSub64F(a []int64) int64 {
	return f64i(i64f(a[0]) - i64f(a[1]))
}

func foldMul8(a []int64) int64 {
	return int64(int8(a[0] * a[1]))
}

func foldMul16(a []int64) int64 {
	return int64(int16(a[0] * a[1]))
}

func foldMul32(a []int64) int64 {
	return int64(int32(a[0] * a[1]))
}

func foldMul64(a []int64) int64 {
	return a[0] * a[1]
}

func foldMul32F(a []int64) int64 {
	return f32i(i32f(a[0]) * i32f(a[1]))
}

func foldMul64F(a []int64) int64 {
	return f64i(i64f(a[0]) * i64f(a[1]))
}

func foldDiv32F(a []int64) int64 {
	return f32i(i32f(a[0]) / i32f(a[1]))
}

func foldDiv64F(a []int64) int64 {
	return f64i(i64f(a[0]) / i64f(a[1]))
}

// Division and modulo functions fold only operations with a constant
// non-zero divisor, otherwise the value is considered non-constant and
// the runtime is left to handle the division by zero.
func foldDiv8(k []latticeKind, a []int64) latticeValue {
	if k[0] == latticeBottom || k[1] == latticeBottom {
		return latticeValue{kind: latticeBottom}
	}
	if k[0] == latticeTop || k[1] == latticeTop {
		return latticeValue{kind: latticeTop}
	}
	if k[1] == 0 {
		return latticeValue{kind: latticeBottom}
	}
	return latticeValue{kind: latticeConst, bits: int64(int8(a[0]) / int8(a[1]))}
}

func foldDiv16(k []latticeKind, a []int64) latticeValue {
	if k[0] == latticeBottom || k[1] == latticeBottom {
		return latticeValue{kind: latticeBottom}
	}
	if k[0] == latticeTop || k[1] == latticeTop {
		return latticeValue{kind: latticeTop}
	}
	if k[1] == 0 {
		return latticeValue{kind: latticeBottom}
	}
	return latticeValue{kind: latticeConst, bits: int64(int16(a[0]) / int16(a[1]))}
}

func foldDiv32(k []latticeKind, a []int64) latticeValue {
	if k[0] == latticeBottom || k[1] == latticeBottom {
		return latticeValue{kind: latticeBottom}
	}
	if k[0] == latticeTop || k[1] == latticeTop {
		return latticeValue{kind: latticeTop}
	}
	if k[1] == 0 {
		return latticeValue{kind: latticeBottom}
	}
	return latticeValue{kind: latticeConst, bits: int64(int32(a[0]) / int32(a[1]))}
}

func foldDiv64(k []latticeKind, a []int64) latticeValue {
	if k[0] == latticeBottom || k[1] == latticeBottom {
		return latticeValue{kind: latticeBottom}
	}
	if k[0] == latticeTop || k[1] == latticeTop {
		return latticeValue{kind: latticeTop}
	}
	if k[1] == 0 {
		return latticeValue{kind: latticeBottom}
	}
	return latticeValue{kind: latticeConst, bits: a[0] / a[1]}
}

func foldDivU8(k []latticeKind, a []int64) latticeValue {
	if k[0] == latticeBottom || k[1] == latticeBottom {
		return latticeValue{kind: latticeBottom}
	}
	if k[0] == latticeTop || k[1] == latticeTop {
		return latticeValue{kind: latticeTop}
	}
	if k[1] == 0 {
		return latticeValue{kind: latticeBottom}
	}
	return latticeValue{kind: latticeConst, bits: int64(int8(uint8(a[0]) / uint8(a[1])))}
}

func foldDivU16(k []latticeKind, a []int64) latticeValue {
	if k[0] == latticeBottom || k[1] == latticeBottom {
		return latticeValue{kind: latticeBottom}
	}
	if k[0] == latticeTop || k[1] == latticeTop {
		return latticeValue{kind: latticeTop}
	}
	if k[1] == 0 {
		return latticeValue{kind: latticeBottom}
	}
	return latticeValue{kind: latticeConst, bits: int64(int16(uint16(a[0]) / uint16(a[1])))}
}

func foldDivU32(k []latticeKind, a []int64) latticeValue {
	if k[0] == latticeBottom || k[1] == latticeBottom {
		return latticeValue{kind: latticeBottom}
	}
	if k[0] == latticeTop || k[1] == latticeTop {
		return latticeValue{kind: latticeTop}
	}
	if k[1] == 0 {
		return latticeValue{kind: latticeBottom}
	}
	return latticeValue{kind: latticeConst, bits: int64(int32(uint32(a[0]) / uint32(a[1])))}
}

func foldDivU64(k []latticeKind, a []int64) latticeValue {
	if k[0] == latticeBottom || k[1] == latticeBottom {
		return latticeValue{kind: latticeBottom}
	}
	if k[0] == latticeTop || k[1] == latticeTop {
		return latticeValue{kind: latticeTop}
	}
	if k[1] == 0 {
		return latticeValue{kind: latticeBottom}
	}
	return latticeValue{kind: latticeConst, bits: int64(uint64(a[0]) / uint64(a[1]))}
}

func foldEq(a []int64) int64 {
	return b2i(a[0] == a[1])
}

func foldNeq(a []int64) int64 {
	return b2i(a[0] != a[1])
}

func foldLess(a []int64) int64 {
	return b2i(a[0] < a[1])
}

func foldLessU(a []int64) int64 {
	return b2i(uint64(a[0]) < uint64(a[1]))
}

func foldLess32F(a []int64) int64 {
	return b2i(i32f(a[0]) < i32f(a[1]))
}

func foldLess64F(a []int64) int64 {
	return b2i(i64f(a[0]) < i64f(a[1]))
}

func foldLeq(a []int64) int64 {
	return b2i(a[0] <= a[1])
}

func foldLeqU(a []int64) int64 {
	return b2i(uint64(a[0]) <= uint64(a[1]))
}

func foldLeq32F(a []int64) int64 {
	return b2i(i32f(a[0]) <= i32f(a[1]))
}

func foldLeq64F(a []int64) int64 {
	return b2i(i64f(a[0]) <= i64f(a[1]))
}

func foldGreater(a []int64) int64 {
	return b2i(a[0] > a[1])
}

func foldGreaterU(a []int64) int64 {
	return b2i(uint64(a[0]) > uint64(a[1]))
}

func foldGreater32F(a []int64) int64 {
	return b2i(i32f(a[0]) > i32f(a[1]))
}

func foldGreater64F(a []int64) int64 {
	return b2i(i64f(a[0]) > i64f(a[1]))
}

func foldGeq(a []int64) int64 {
	return b2i(a[0] >= a[1])
}

func foldGeqU(a []int64) int64 {
	return b2i(uint64(a[0]) >= uint64(a[1]))
}

func foldGeq32F(a []int64) int64 {
	return b2i(i32f(a[0]) >= i32f(a[1]))
}

func foldGeq64F(a []int64) int64 {
	return b2i(i64f(a[0]) >= i64f(a[1]))
}

// foldAndB is a special case: false && <any> == false, <any> && false == false.
func foldAndB(k []latticeKind, a []int64) latticeValue {
	if k[0] == latticeConst && a[0] == 0 || k[1] == latticeConst && a[1] == 0 {
		return latticeValue{kind: latticeConst, bits: 0}
	}
	if k[0] == latticeBottom || k[1] == latticeBottom {
		return latticeValue{kind: latticeBottom}
	}
	if k[0] == latticeTop || k[1] == latticeTop {
		return latticeValue{kind: latticeTop}
	}
	return latticeValue{kind: latticeConst, bits: b2i(a[0] != 0 && a[1] != 0)}
}

// foldOrB is a special case: true || <any> == true, <any> || true == true.
func foldOrB(k []latticeKind, a []int64) latticeValue {
	if k[0] == latticeConst && a[0] == 1 || k[1] == latticeConst && a[1] == 1 {
		return latticeValue{kind: latticeConst, bits: 1}
	}
	if k[0] == latticeBottom || k[1] == latticeBottom {
		return latticeValue{kind: latticeBottom}
	}
	if k[0] == latticeTop || k[1] == latticeTop {
		return latticeValue{kind: latticeTop}
	}
	return latticeValue{kind: latticeConst, bits: b2i(a[0] != 0 || a[1] != 0)}
}

func foldNot(a []int64) int64 {
	return b2i(a[0] == 0)
}

func foldNeg(a []int64) int64 {
	return -a[0]
}

func foldNeg32F(a []int64) int64 {
	return f32i(-i32f(a[0]))
}

func foldNeg64F(a []int64) int64 {
	return f64i(-i64f(a[0]))
}

func foldCom(a []int64) int64 {
	return ^a[0]
}

func foldCopy(a []int64) int64 {
	return a[0]
}

func foldSignExt8(a []int64) int64 {
	return int64(int8(a[0]))
}

func foldSignExt16(a []int64) int64 {
	return int64(int16(a[0]))
}

func foldSignExt32(a []int64) int64 {
	return int64(int32(a[0]))
}

func foldZeroExt8(a []int64) int64 {
	return int64(uint8(a[0]))
}

func foldZeroExt16(a []int64) int64 {
	return int64(uint16(a[0]))
}

func foldZeroExt32(a []int64) int64 {
	return int64(uint32(a[0]))
}

func foldTruncTo8(a []int64) int64 {
	return int64(int8(a[0]))
}

func foldTruncTo16(a []int64) int64 {
	return int64(int16(a[0]))
}

func foldTruncTo32(a []int64) int64 {
	return int64(int32(a[0]))
}

func foldCvt32to32F(a []int64) int64 {
	return f32i(float32(int32(a[0])))
}

func foldCvt32to64F(a []int64) int64 {
	return f64i(float64(int32(a[0])))
}

func foldCvt64to32F(a []int64) int64 {
	return f32i(float32(a[0]))
}

func foldCvt64to64F(a []int64) int64 {
	return f64i(float64(a[0]))
}

func foldCvt32Fto32(a []int64) int64 {
	return int64(int32(i32f(a[0])))
}

func foldCvt32Fto64(a []int64) int64 {
	return int64(i32f(a[0]))
}

func foldCvt64Fto32(a []int64) int64 {
	return int64(int32(i64f(a[0])))
}

func foldCvt64Fto64(a []int64) int64 {
	return int64(i64f(a[0]))
}

func foldCvt32Uto32F(a []int64) int64 {
	return f32i(float32(uint32(a[0])))
}

func foldCvt32Uto64F(a []int64) int64 {
	return f64i(float64(uint32(a[0])))
}

func foldCvt32Fto32U(a []int64) int64 {
	return int64(int32(uint32(i32f(a[0]))))
}

func foldCvt64Fto32U(a []int64) int64 {
	return int64(int32(uint32(i64f(a[0]))))
}

func foldCvt64Uto32F(a []int64) int64 {
	return f32i(float32(uint64(a[0])))
}

func foldCvt64Uto64F(a []int64) int64 {
	return f64i(float64(uint64(a[0])))
}

func foldCvt32Fto64U(a []int64) int64 {
	return int64(uint64(i32f(a[0])))
}

func foldCvt64Fto64U(a []int64) int64 {
	return int64(uint64(i64f(a[0])))
}

func isConst(op Op) bool {
	return op == OpConstBool || OpConst8 <= op && op <= OpConst64
}

// Table of fold functions.

func getFoldFn(op Op) (foldFn, bool) {
	i := int(op - OpAdd8)
	if i >= len(foldMap) || foldMap[i].fn == nil && foldMap[i].genFn == nil {
		return foldFn{}, false
	}
	return foldMap[i], true
}

type foldFn struct {
	// General fold function.
	genFn func([]latticeKind, []int64) latticeValue
	// Fold function when all of the arguments are constant.
	fn func([]int64) int64
}

var foldMap = [...]foldFn{
	OpAdd8 - OpAdd8:  {fn: foldAdd8},
	OpAdd16 - OpAdd8: {fn: foldAdd16},
	OpAdd32 - OpAdd8: {fn: foldAdd32},
	OpAdd64 - OpAdd8: {fn: foldAdd64},
	//	OpAddPtr  NOPE

	OpAdd32F - OpAdd8: {fn: foldAdd32F},
	OpAdd64F - OpAdd8: {fn: foldAdd64F},

	OpSub8 - OpAdd8:  {fn: foldSub8},
	OpSub16 - OpAdd8: {fn: foldSub16},
	OpSub32 - OpAdd8: {fn: foldSub32},
	OpSub64 - OpAdd8: {fn: foldSub64},
	//	OpSubPtr  NOPE
	OpSub32F - OpAdd8: {fn: foldSub32F},
	OpSub64F - OpAdd8: {fn: foldSub64F},

	OpMul8 - OpAdd8:   {fn: foldMul8},
	OpMul16 - OpAdd8:  {fn: foldMul16},
	OpMul32 - OpAdd8:  {fn: foldMul32},
	OpMul64 - OpAdd8:  {fn: foldMul64},
	OpMul32F - OpAdd8: {fn: foldMul32F},
	OpMul64F - OpAdd8: {fn: foldMul64F},
	OpDiv32F - OpAdd8: {fn: foldDiv32F},
	OpDiv64F - OpAdd8: {fn: foldDiv64F},
	// OpHmul8: TODO
	// OpHmul8u
	// OpHmul16
	// OpHmul16u
	// OpHmul32
	// OpHmul32u
	// OpHmul64
	// OpHmul64u
	// OpMul32uhilo
	// OpMul64uhilo
	// OpAvg64u
	OpDiv8 - OpAdd8:   {genFn: foldDiv8},
	OpDiv16 - OpAdd8:  {genFn: foldDiv16},
	OpDiv32 - OpAdd8:  {genFn: foldDiv32},
	OpDiv64 - OpAdd8:  {genFn: foldDiv64},
	OpDiv8u - OpAdd8:  {genFn: foldDivU8},
	OpDiv16u - OpAdd8: {genFn: foldDivU16},
	OpDiv32u - OpAdd8: {genFn: foldDivU32},
	OpDiv64u - OpAdd8: {genFn: foldDivU64},
	// OpDiv128u
	// OpMod8: TODO
	// OpMod8u
	// OpMod16
	// OpMod16u
	// OpMod32
	// OpMod32u
	// OpMod64
	// OpMod64u

	// OpAnd8
	// OpAnd16
	// OpAnd32
	// OpAnd64
	// OpOr8
	// OpOr16
	// OpOr32
	// OpOr64
	// OpXor8
	// OpXor16
	// OpXor32
	// OpXor64
	// OpLsh8x8
	// OpLsh8x16
	// OpLsh8x32
	// OpLsh8x64
	// OpLsh16x8
	// OpLsh16x16
	// OpLsh16x32
	// OpLsh16x64
	// OpLsh32x8
	// OpLsh32x16
	// OpLsh32x32
	// OpLsh32x64
	// OpLsh64x8
	// OpLsh64x16
	// OpLsh64x32
	// OpLsh64x64
	// OpRsh8x8
	// OpRsh8x16
	// OpRsh8x32
	// OpRsh8x64
	// OpRsh16x8
	// OpRsh16x16
	// OpRsh16x32
	// OpRsh16x64
	// OpRsh32x8
	// OpRsh32x16
	// OpRsh32x32
	// OpRsh32x64
	// OpRsh64x8
	// OpRsh64x16
	// OpRsh64x32
	// OpRsh64x64
	// OpRsh8Ux8
	// OpRsh8Ux16
	// OpRsh8Ux32
	// OpRsh8Ux64
	// OpRsh16Ux8
	// OpRsh16Ux16
	// OpRsh16Ux32
	// OpRsh16Ux64
	// OpRsh32Ux8
	// OpRsh32Ux16
	// OpRsh32Ux32
	// OpRsh32Ux64
	// OpRsh64Ux8
	// OpRsh64Ux16
	// OpRsh64Ux32
	// OpRsh64Ux64
	// OpLrot8
	// OpLrot16
	// OpLrot32
	// OpLrot64

	OpEq8 - OpAdd8:  {fn: foldEq},
	OpEq16 - OpAdd8: {fn: foldEq},
	OpEq32 - OpAdd8: {fn: foldEq},
	OpEq64 - OpAdd8: {fn: foldEq},
	//	OpEqPtr NOPE
	//	OpEqInter
	//	OpEqSlice
	OpEq32F - OpAdd8: {fn: foldEq},
	OpEq64F - OpAdd8: {fn: foldEq},
	OpNeq8 - OpAdd8:  {fn: foldNeq},
	OpNeq16 - OpAdd8: {fn: foldNeq},
	OpNeq32 - OpAdd8: {fn: foldNeq},
	OpNeq64 - OpAdd8: {fn: foldNeq},
	//	OpNeqPtr NOPE
	//	OpNeqInter
	//	OpNeqSlice
	OpNeq32F - OpAdd8:  {fn: foldNeq},
	OpNeq64F - OpAdd8:  {fn: foldNeq},
	OpLess8 - OpAdd8:   {fn: foldLess},
	OpLess16 - OpAdd8:  {fn: foldLess},
	OpLess32 - OpAdd8:  {fn: foldLess},
	OpLess64 - OpAdd8:  {fn: foldLess},
	OpLess8U - OpAdd8:  {fn: foldLessU},
	OpLess16U - OpAdd8: {fn: foldLessU},
	OpLess32U - OpAdd8: {fn: foldLessU},
	OpLess64U - OpAdd8: {fn: foldLessU},
	OpLess32F - OpAdd8: {fn: foldLess32F},
	OpLess64F - OpAdd8: {fn: foldLess64F},
	OpLeq8 - OpAdd8:    {fn: foldLeq},
	OpLeq16 - OpAdd8:   {fn: foldLeq},
	OpLeq32 - OpAdd8:   {fn: foldLeq},
	OpLeq64 - OpAdd8:   {fn: foldLeq},
	OpLeq8U - OpAdd8:   {fn: foldLeqU},
	OpLeq16U - OpAdd8:  {fn: foldLeqU},
	OpLeq32U - OpAdd8:  {fn: foldLeqU},
	OpLeq64U - OpAdd8:  {fn: foldLeqU},
	OpLeq32F - OpAdd8:  {fn: foldLeq32F},
	OpLeq64F - OpAdd8:  {fn: foldLeq64F},

	OpGreater8 - OpAdd8:   {fn: foldGreater},
	OpGreater16 - OpAdd8:  {fn: foldGreater},
	OpGreater32 - OpAdd8:  {fn: foldGreater},
	OpGreater64 - OpAdd8:  {fn: foldGreater},
	OpGreater8U - OpAdd8:  {fn: foldGreaterU},
	OpGreater16U - OpAdd8: {fn: foldGreaterU},
	OpGreater32U - OpAdd8: {fn: foldGreaterU},
	OpGreater64U - OpAdd8: {fn: foldGreaterU},
	OpGreater32F - OpAdd8: {fn: foldGreater32F},
	OpGreater64F - OpAdd8: {fn: foldGreater64F},

	OpGeq8 - OpAdd8:  {fn: foldGeq},
	OpGeq16 - OpAdd8: {fn: foldGeq},
	OpGeq32 - OpAdd8: {fn: foldGeq},
	OpGeq64 - OpAdd8: {fn: foldGeq},

	OpGeq8U - OpAdd8:  {fn: foldGeqU},
	OpGeq16U - OpAdd8: {fn: foldGeqU},
	OpGeq32U - OpAdd8: {fn: foldGeqU},
	OpGeq64U - OpAdd8: {fn: foldGeqU},
	OpGeq32F - OpAdd8: {fn: foldGeq32F},
	OpGeq64F - OpAdd8: {fn: foldGeq64F},

	OpAndB - OpAdd8: {genFn: foldAndB},
	OpOrB - OpAdd8:  {genFn: foldOrB},

	OpEqB - OpAdd8:    {fn: foldEq},
	OpNeqB - OpAdd8:   {fn: foldNeq},
	OpNot - OpAdd8:    {fn: foldNot},
	OpNeg8 - OpAdd8:   {fn: foldNeg},
	OpNeg16 - OpAdd8:  {fn: foldNeg},
	OpNeg32 - OpAdd8:  {fn: foldNeg},
	OpNeg64 - OpAdd8:  {fn: foldNeg},
	OpNeg32F - OpAdd8: {fn: foldNeg32F},
	OpNeg64F - OpAdd8: {fn: foldNeg64F},
	OpCom8 - OpAdd8:   {fn: foldCom},
	OpCom16 - OpAdd8:  {fn: foldCom},
	OpCom32 - OpAdd8:  {fn: foldCom},
	OpCom64 - OpAdd8:  {fn: foldCom},
	// OpCtz32 TODO
	// OpCtz64
	// OpBswap32
	// OpBswap64
	// OpSqrt

	// OpPhi
	OpCopy - OpAdd8: {fn: foldCopy},

	// OpConvert  NOPE-NOPE-NOPE
	// OpConstBool
	// OpConstString
	// OpConstNil
	// OpConst8
	// OpConst16
	// OpConst32
	// OpConst64
	// OpConst32F
	// OpConst64F
	// OpConstInterface
	// OpConstSlice
	// OpInitMem
	// OpArg
	// OpAddr
	// OpSP
	// OpSB
	// OpFunc
	// OpLoad
	// OpStore
	// OpMove
	// OpZero
	// OpClosureCall
	// OpStaticCall
	// OpDeferCall
	// OpGoCall
	// OpInterCall

	OpSignExt8to16 - OpAdd8:  {fn: foldSignExt8},
	OpSignExt8to32 - OpAdd8:  {fn: foldSignExt8},
	OpSignExt8to64 - OpAdd8:  {fn: foldSignExt8},
	OpSignExt16to32 - OpAdd8: {fn: foldSignExt16},
	OpSignExt16to64 - OpAdd8: {fn: foldSignExt16},
	OpSignExt32to64 - OpAdd8: {fn: foldSignExt32},

	OpZeroExt8to16 - OpAdd8:  {fn: foldZeroExt8},
	OpZeroExt8to32 - OpAdd8:  {fn: foldZeroExt8},
	OpZeroExt8to64 - OpAdd8:  {fn: foldZeroExt8},
	OpZeroExt16to32 - OpAdd8: {fn: foldZeroExt16},
	OpZeroExt16to64 - OpAdd8: {fn: foldZeroExt16},
	OpZeroExt32to64 - OpAdd8: {fn: foldZeroExt32},

	OpTrunc16to8 - OpAdd8:  {fn: foldTruncTo8},
	OpTrunc32to8 - OpAdd8:  {fn: foldTruncTo8},
	OpTrunc64to8 - OpAdd8:  {fn: foldTruncTo8},
	OpTrunc32to16 - OpAdd8: {fn: foldTruncTo16},
	OpTrunc64to16 - OpAdd8: {fn: foldTruncTo16},
	OpTrunc64to32 - OpAdd8: {fn: foldTruncTo32},

	OpCvt32to32F - OpAdd8: {fn: foldCvt32to32F},
	OpCvt32to64F - OpAdd8: {fn: foldCvt32to64F},

	OpCvt64to32F - OpAdd8: {fn: foldCvt64to32F},
	OpCvt64to64F - OpAdd8: {fn: foldCvt64to64F},

	OpCvt32Fto32 - OpAdd8: {fn: foldCvt32Fto32},
	OpCvt32Fto64 - OpAdd8: {fn: foldCvt32Fto64},

	OpCvt64Fto32 - OpAdd8: {fn: foldCvt64Fto32},
	OpCvt64Fto64 - OpAdd8: {fn: foldCvt64Fto64},

	OpCvt32Fto64F - OpAdd8: {fn: foldCvt32Fto32},
	OpCvt64Fto32F - OpAdd8: {fn: foldCvt32Fto32},

	// OpIsNonNil NOPE-NOPE-NOPE
	// OpIsInBounds
	// OpIsSliceInBounds
	// OpNilCheck
	// OpGetG
	// OpGetClosurePtr
	// OpArrayIndex
	// OpPtrIndex
	// OpOffPtr
	// OpSliceMake
	// OpSlicePtr
	// OpSliceLen
	// OpSliceCap
	// OpComplexMake
	// OpComplexReal
	// OpComplexImag
	// OpStringMake
	// OpStringPtr
	// OpStringLen
	// OpIMake
	// OpITab
	// OpIData
	// OpStructMake0
	// OpStructMake1
	// OpStructMake2
	// OpStructMake3

	// OpStructMake4
	// OpStructSelect
	// OpStoreReg
	// OpLoadReg
	// OpFwdRef
	// OpUnknown
	// OpVarDef
	// OpVarKill
	// OpVarLive
	// OpKeepAlive
	// OpInt64Make
	// OpInt64Hi
	// OpInt64Lo

	// OpAdd32carry TODO
	// OpAdd32withcarry
	// OpSub32carry
	// OpSub32withcarry
	// OpMul32uhilo

	// OpSignmask TODO
	// OpZeromask

	OpCvt32Uto32F - OpAdd8: {fn: foldCvt32Uto32F},
	OpCvt32Uto64F - OpAdd8: {fn: foldCvt32Uto64F},
	OpCvt32Fto32U - OpAdd8: {fn: foldCvt32Fto32U},
	OpCvt64Fto32U - OpAdd8: {fn: foldCvt64Fto32U},
	OpCvt64Uto32F - OpAdd8: {fn: foldCvt64Uto32F},
	OpCvt64Uto64F - OpAdd8: {fn: foldCvt64Uto64F},
	OpCvt32Fto64U - OpAdd8: {fn: foldCvt32Fto64U},
	OpCvt64Fto64U - OpAdd8: {fn: foldCvt64Fto64U},

	// OpSelect0 NOPE-NOPE-NOPE
	// OpSelect1
	// OpAtomicLoad32
	// OpAtomicLoad64
	// OpAtomicLoadPtr
	// OpAtomicStore32
	// OpAtomicStore64
	// OpAtomicStorePtrNoWB
	// OpAtomicExchange32
	// OpAtomicExchange64
	// OpAtomicAdd32
	// OpAtomicAdd64
	// OpAtomicCompareAndSwap32
	// OpAtomicCompareAndSwap64
	// OpAtomicAnd8
	// OpAtomicOr8
}
