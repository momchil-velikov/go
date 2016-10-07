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

	// If the loop contains calls, moving an invariant outside the loop
	// would likely increase spills. FIXME: need to weigh the cost of
	// spill/reload against the cost of evaluating some big invariant.
	if lp.containsCall {
		return
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
	// Do not hoist control values. They are always live and the
	// compiler may put the original value back, in effect increasing
	// code size and execution time.
	if v == v.Block.Control {
		return false
	}

	// Do not hoist operations, which modify memory. If there are memory
	// writes in the loop, the loop would contain a `Phi<mem>` in the
	// header and this operation will depend (transitively) on it.  The
	// check here, while not strictly necessary, is a shortcut
	// alternative to following the use-def chain up to that `Phi<mem>`.
	if v.Type.IsMemory() {
		return false
	}

	return true
}

var (
	specSafeV = [...]Op{

		OpAdd8, OpAdd16, OpAdd32, OpAdd64, OpAddPtr, OpAdd32F, OpAdd64F,

		OpSub8, OpSub16, OpSub32, OpSub64, OpSubPtr, OpSub32F, OpSub64,

		OpMul8, OpMul16, OpMul32, OpMul64, OpMul32F, OpMul64F,

		OpHmul8, OpHmul8u, OpHmul16, OpHmul16u, OpHmul32, OpHmul32u, OpHmul64, OpHmul64u,

		OpAvg64u,

		OpAnd8, OpAnd16, OpAnd32, OpAnd64,

		OpOr8, OpOr16, OpOr32, OpOr64,

		OpXor8, OpXor16, OpXor32, OpXor64,

		OpLsh8x8, OpLsh8x16, OpLsh8x32, OpLsh8x64,

		OpLsh16x8, OpLsh16x16, OpLsh16x32, OpLsh16x64,

		OpLsh32x8, OpLsh32x16, OpLsh32x32, OpLsh32x64,

		OpLsh64x8, OpLsh64x16, OpLsh64x32, OpLsh64x64,

		OpRsh8x8, OpRsh8x16, OpRsh8x32, OpRsh8x64,

		OpRsh16x8, OpRsh16x16, OpRsh16x32, OpRsh16x64,

		OpRsh32x8, OpRsh32x16, OpRsh32x32, OpRsh32x64,

		OpRsh64x8, OpRsh64x16, OpRsh64x32, OpRsh64x64,

		OpRsh8Ux8, OpRsh8Ux16, OpRsh8Ux32, OpRsh8Ux64,

		OpRsh16Ux8, OpRsh16Ux16, OpRsh16Ux32, OpRsh16Ux64,

		OpRsh32Ux8, OpRsh32Ux16, OpRsh32Ux32, OpRsh32Ux64,

		OpRsh64Ux8, OpRsh64Ux16, OpRsh64Ux32, OpRsh64Ux64,

		OpLrot8, OpLrot16, OpLrot32, OpLrot64,

		OpEq8, OpEq16, OpEq32, OpEq64, OpEqPtr,

		// OpEqInter, OpEqSlice

		OpEq32F, OpEq64F,

		OpNeq8, OpNeq16, OpNeq32, OpNeq64, OpNeqPtr,

		// OpNeqInter, OpNeqSlice,

		OpNeq32F, OpNeq64F,

		OpLess8, OpLess8U, OpLess16, OpLess16U, OpLess32, OpLess32U, OpLess64, OpLess64U, OpLess32F, OpLess64F,

		OpLeq8, OpLeq8U, OpLeq16, OpLeq16U, OpLeq32, OpLeq32U, OpLeq64, OpLeq64U, OpLeq32F, OpLeq64F,

		OpGreater8, OpGreater8U, OpGreater16, OpGreater16U, OpGreater32, OpGreater32U, OpGreater64, OpGreater64U,

		OpGreater32F, OpGreater64F,

		OpGeq8, OpGeq8U, OpGeq16, OpGeq16U, OpGeq32, OpGeq32U, OpGeq64, OpGeq64U, OpGeq32F, OpGeq64F,

		OpAndB, OpOrB, OpEqB, OpNeqB, OpNot,

		OpNeg8, OpNeg16, OpNeg32, OpNeg64, OpNeg32F, OpNeg64F,

		OpCom8, OpCom16, OpCom32, OpCom64,

		OpCtz32, OpCtz64,

		OpBswap32, OpBswap64,

		// OpSqrt, 	OpPhi

		OpCopy,

		// OpConvert

		OpConstBool, OpConstString, OpConstNil, OpConst8, OpConst16, OpConst32, OpConst64, OpConst32F, OpConst64F,

		OpConstInterface, OpConstSlice,

		// OpInitMem,	OpArg,

		// OpAddr, OpSP, OpSB,

		// OpFunc,

		// OpLoad,	OpStore, OpMove, OpZero

		// OpClosureCall, OpStaticCall, OpDeferCall, OpGoCall, OpInterCall,

		OpSignExt8to16, OpSignExt8to32, OpSignExt8to64, OpSignExt16to32, OpSignExt16to64, OpSignExt32to64,

		OpZeroExt8to16, OpZeroExt8to32, OpZeroExt8to64, OpZeroExt16to32, OpZeroExt16to64, OpZeroExt32to64,

		OpTrunc16to8, OpTrunc32to8, OpTrunc32to16, OpTrunc64to8, OpTrunc64to16, OpTrunc64to32,

		OpCvt32to32F, OpCvt32to64F, OpCvt64to32F, OpCvt64to64F,
		OpCvt32Fto32, OpCvt32Fto64, OpCvt64Fto32, OpCvt64Fto64, OpCvt32Fto64F, OpCvt64Fto32F,

		// OpIsNonNil, OpIsInBounds, OpIsSliceInBounds, OpNilCheck

		// OpGetG, OpGetClosurePtr,	OpArrayIndex,	OpPtrIndex,	OpOffPtr

		// OpSliceMake

		OpSlicePtr, OpSliceLen, OpSliceCap,

		OpComplexMake, OpComplexReal, OpComplexImag,

		// OpStringMake

		OpStringPtr, OpStringLen,

		// OpIMake

		OpITab, OpIData,

		OpStructMake0, OpStructMake1, OpStructMake2, OpStructMake3, OpStructMake4,

		OpStructSelect,

		// OpStoreReg,	OpLoadReg

		// OpFwdRef

		// OpUnknown

		// OpVarDef,	OpVarKill,	OpVarLive,	OpKeepAlive,

		OpInt64Make, OpInt64Hi, OpInt64Lo,

		// OpAdd32carry, OpAdd32withcarry, OpSub32carry, OpSub32withcarry,

		OpMul32uhilo,

		OpSignmask, OpZeromask,

		OpCvt32Uto32F, OpCvt32Uto64F, OpCvt32Fto32U, OpCvt64Fto32U,
		OpCvt64Uto32F, OpCvt64Uto64F, OpCvt32Fto64U, OpCvt64Fto64U,

		OpSelect0, OpSelect1,

		// OpAtomicLoad32, OpAtomicLoad64, OpAtomicLoadPtr,

		// OpAtomicStore32, OpAtomicStore64, OpAtomicStorePtrNoWB,

		// OpAtomicExchange32, OpAtomicExchange64,

		// OpAtomicAdd32, OpAtomicAdd64,

		// OpAtomicCompareAndSwap32, OpAtomicCompareAndSwap64,

		// OpAtomicAnd8, OpAtomicOr8,
	}

	specSafe = map[Op]struct{}{}
)

func init() {
	for _, v := range specSafeV {
		specSafe[v] = struct{}{}
	}
}

// specExecSafe returns true if `op` can be safely executed by the
// optimized program, even though it may not be executed in the original
// program at all.
func specExecSafe(v *Value) bool {
	if _, ok := specSafe[v.Op]; ok {
		return true
	}

	// Allow division and modulo operations with constant non-zero
	// divisors.
	if v.Op == OpDiv32F || v.Op == OpDiv64F || OpDiv8 <= v.Op && v.Op <= OpDiv64u || OpMod8 <= v.Op && v.Op <= OpMod64u {
		a := v.Args[1]
		return OpConst8 <= a.Op && a.Op <= OpConst64F && a.AuxInt == 0
	}

	return false
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

	// Some operations are safe to execute speculatively.
	if specExecSafe(v) {
		goto invariant
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
