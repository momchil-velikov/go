package ssa

import "fmt"

func licm(f *Func) {
	ln := f.loopnest()
	ln.assembleChildren()
	ln.findExits()

	// Pass statistics.
	nmove := 0    // number of invariants moved
	noprehdr := 0 // number of loops with no pre-header

	for _, lp := range ln.loops {
		if lp.outer == nil {
			n, h := moveInvariants(ln, lp)
			nmove += n
			noprehdr += h
		}
	}

	if f.pass.stats > 0 {
		f.LogStat("LICM MOVES", nmove)
		f.LogStat("LICM NOPREHDR", noprehdr)
	}
}

func isNestedLoop(inner, outer *loop) bool {
	for inner != nil && inner != outer {
		inner = inner.outer
	}
	return inner == outer
}

// Map of invariant Values
// - not present: unknown
// - true : loop invariant
// - false: loop dependent
type invmap map[ID]bool

func moveInvariants(ln *loopnest, lp *loop) (nmove, nohdr int) {
	if !lp.isInner {
		// First move invariants out of the inner loops.
		for _, c := range lp.children {
			n, h := moveInvariants(ln, c)
			nmove += n
			nohdr += h
		}
	}

	// Find the pre-header. It's the only edge, coming from a block, not
	// dominated by the loop header, i.e. not in the loop.
	var pre *Block
	sdom := ln.f.sdom()
	for _, e := range lp.header.Preds {
		if sdom.isAncestorEq(lp.header, e.b) {
			continue
		}
		if pre != nil {
			pre = nil
			break
		}
		pre = e.b
	}

	// Check we in fact have a pre-header.
	if pre == nil {
		nohdr++
		return
	}

	// Determine invariance of each definition in the loop.
	inv := make(invmap)
	for _, b := range ln.f.Blocks {
		if ln.b2l[b.ID] != lp {
			continue
		}
		for _, v := range b.Values {
			checkInvariant(ln, lp, v, inv)
		}
	}

	if ln.f.pass.debug > 1 {
		fmt.Printf("loop %s invariants:", lp.header)
		for id, isInv := range inv {
			if isInv {
				fmt.Printf(" v%d", id)
			}
		}
		fmt.Println()
	}

	// Move the invariants to the pre-header.
	for _, b := range ln.f.Blocks {
		if ln.b2l[b.ID] != lp {
			continue
		}
		n := 0
		for _, v := range b.Values {
			isInv, ok := inv[v.ID]
			if !ok {
				ln.f.Fatalf("unknown invariance status for %s", v)
			}
			if !isInv {
				b.Values[n] = v
				n++
				continue
			}
			pre.Values = append(pre.Values, v)
			v.Block = pre
			nmove++
		}
		b.Values = b.Values[:n]
	}
	return
}

func canHoistValue(v *Value) bool {
	// φ-ops are not invariant.
	if v.Op == OpPhi {
		return false
	}
	// Do not hoist values with memory args.
	for _, a := range v.Args {
		if a.Type.IsMemory() {
			return false
		}
	}
	// Do not hoist control values. They are always live and the
	// compiler may put the original value back, in effect increasing
	// code size and execution time.
	// FIXME(chill): check this
	if v == v.Block.Control {
		return false
	}
	return true
}

func checkInvariant(ln *loopnest, lp *loop, v *Value, inv invmap) bool {
	sdom := ln.f.sdom()

	// Check if we already know the invariance status.
	if isInv, ok := inv[v.ID]; ok {
		return isInv
	}

	// If the Value is defined outside the loop it is invariant iff it
	// dominates the loop header.
	if ln.b2l[v.Block.ID] != lp {
		return sdom.isAncestor(v.Block, lp.header)
	}

	// Certain operations are never moved and the corresponding values
	// are considered not invariant.
	if !canHoistValue(v) {
		goto notInvariant
	}

	// If the value is a constant, it is an invariant.
	if OpConstBool <= v.Op && v.Op <= OpConstSlice {
		goto invariant
	}

	// Figure out the invariant status of the arguments.
	for _, a := range v.Args {
		if !checkInvariant(ln, lp, a, inv) {
			goto notInvariant
		}
	}

	// Check the value dominates all loop exit blocks, except the ones
	// of the BlockExit kind.
	for _, b := range lp.exits {
		if b.Kind != BlockExit && !sdom.isAncestor(v.Block, b) {
			goto notInvariant
		}
	}

invariant:
	inv[v.ID] = true
	return true

notInvariant:
	inv[v.ID] = false
	return false
}
