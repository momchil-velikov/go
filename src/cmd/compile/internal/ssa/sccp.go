package ssa

import (
	"fmt"
	"math"
)

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
	ssalist  []*Value
}

func sccp(f *Func) {
	if f.pass.debug > 1 {
		fmt.Printf("SCCP func %s:\n", f.Name)
	}

	s := sccpState{
		f:     f,
		cells: make([]latticeCell, f.NumValues()),
		exec:  make(map[Edge]bool),
	}
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

	s.visitExprs(f.Entry)
	for len(s.flowlist) > 0 || len(s.ssalist) > 0 {
		switch {
		case len(s.flowlist) > 0:
			e := s.flowlist[len(s.flowlist)-1]
			s.flowlist = s.flowlist[:len(s.flowlist)-1]
			if s.exec[e] {
				continue
			}
			s.exec[e] = true

			tmp := [4]bool{}
			x, n := s.execEdges(e.b, tmp[:0])
			s.visitPhis(e.b.Preds[e.i].b, e.b, x)

			if n > 1 {
				continue
			}
			s.visitExprs(e.b)

		case len(s.ssalist) > 0:
			v := s.ssalist[len(s.ssalist)-1]
			s.ssalist = s.ssalist[:len(s.ssalist)-1]

			tmp := [4]bool{}
			x, n := s.execEdges(v.Block, tmp[:0])

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
	if b.Kind == BlockPlain {
		s.flowlist = append(s.flowlist, b.Succs[0])
	}
}

func (s *sccpState) visitExpr(v *Value) {
	new := latticeValue{}
	if isConst(v.Op) {
		new = latticeValue{kind: latticeConst, bits: v.AuxInt}
	} else {
		tmpKind := [2]latticeKind{}
		tmpArgs := [2]int64{}
		kinds := tmpKind[:0]
		args := tmpArgs[:0]
		ntop, nbot := 0, 0
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
		if t, ok := foldMap[v.Op]; ok {
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
		} else {
			new.kind = latticeBottom
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

func (s *sccpState) propagate(v *Value) {
	for _, u := range s.cells[v.ID].use {
		s.ssalist = append(s.ssalist, u)
	}
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

type foldFn struct {
	fn    func([]int64) int64                       // fold function for CONST only
	genFn func([]latticeKind, []int64) latticeValue // general fold function
}

var foldMap = map[Op]foldFn{
	OpAdd8:  {fn: foldAdd8},
	OpAdd16: {fn: foldAdd16},
	OpAdd32: {fn: foldAdd32},
	OpAdd64: {fn: foldAdd64},
	//	OpAddPtr  NOPE

	OpAdd32F: {fn: foldAdd32F},
	OpAdd64F: {fn: foldAdd64F},

	OpSub8:  {fn: foldSub8},
	OpSub16: {fn: foldSub16},
	OpSub32: {fn: foldSub32},
	OpSub64: {fn: foldSub64},
	//	OpSubPtr  NOPE
	OpSub32F: {fn: foldSub32F},
	OpSub64F: {fn: foldSub64F},

	OpMul8:   {fn: foldMul8},
	OpMul16:  {fn: foldMul16},
	OpMul32:  {fn: foldMul32},
	OpMul64:  {fn: foldMul64},
	OpMul32F: {fn: foldMul32F},
	OpMul64F: {fn: foldMul64F},
	OpDiv32F: {fn: foldDiv32F},
	OpDiv64F: {fn: foldDiv64F},
	// OpHmul8: TODO
	// OpHmul8u
	// OpHmul16
	// OpHmul16u
	// OpHmul32
	// OpHmul32u
	// OpHmul64
	// OpHmul64u
	// OpAvg64u
	OpDiv8:   {genFn: foldDiv8},
	OpDiv16:  {genFn: foldDiv16},
	OpDiv32:  {genFn: foldDiv32},
	OpDiv64:  {genFn: foldDiv64},
	OpDiv8u:  {genFn: foldDivU8},
	OpDiv16u: {genFn: foldDivU16},
	OpDiv32u: {genFn: foldDivU32},
	OpDiv64u: {genFn: foldDivU64},
	// OpMod8: TODO
	// OpMod8u
	// OpMod16
	// OpMod16u
	// OpMod32
	// OpMod32u
	// OpMod64
	// OpMod64u
	OpEq8:  {fn: foldEq},
	OpEq16: {fn: foldEq},
	OpEq32: {fn: foldEq},
	OpEq64: {fn: foldEq},
	//	OpEqPtr NOPE
	//	OpEqInter
	//	OpEqSlice
	OpEq32F: {fn: foldEq},
	OpEq64F: {fn: foldEq},
	OpNeq8:  {fn: foldNeq},
	OpNeq16: {fn: foldNeq},
	OpNeq32: {fn: foldNeq},
	OpNeq64: {fn: foldNeq},
	//	OpNeqPtr NOPE
	//	OpNeqInter
	//	OpNeqSlice
	OpNeq32F:  {fn: foldNeq},
	OpNeq64F:  {fn: foldNeq},
	OpLess8:   {fn: foldLess},
	OpLess16:  {fn: foldLess},
	OpLess32:  {fn: foldLess},
	OpLess64:  {fn: foldLess},
	OpLess8U:  {fn: foldLessU},
	OpLess16U: {fn: foldLessU},
	OpLess32U: {fn: foldLessU},
	OpLess64U: {fn: foldLessU},
	OpLess32F: {fn: foldLess32F},
	OpLess64F: {fn: foldLess64F},
	OpLeq8:    {fn: foldLeq},
	OpLeq16:   {fn: foldLeq},
	OpLeq32:   {fn: foldLeq},
	OpLeq64:   {fn: foldLeq},
	OpLeq8U:   {fn: foldLeqU},
	OpLeq16U:  {fn: foldLeqU},
	OpLeq32U:  {fn: foldLeqU},
	OpLeq64U:  {fn: foldLeqU},
	OpLeq32F:  {fn: foldLeq32F},
	OpLeq64F:  {fn: foldLeq64F},

	OpGreater8:   {fn: foldGreater},
	OpGreater16:  {fn: foldGreater},
	OpGreater32:  {fn: foldGreater},
	OpGreater64:  {fn: foldGreater},
	OpGreater8U:  {fn: foldGreaterU},
	OpGreater16U: {fn: foldGreaterU},
	OpGreater32U: {fn: foldGreaterU},
	OpGreater64U: {fn: foldGreaterU},
	OpGreater32F: {fn: foldGreater32F},
	OpGreater64F: {fn: foldGreater64F},

	OpGeq8:  {fn: foldGeq},
	OpGeq16: {fn: foldGeq},
	OpGeq32: {fn: foldGeq},
	OpGeq64: {fn: foldGeq},

	OpGeq8U:  {fn: foldGeqU},
	OpGeq16U: {fn: foldGeqU},
	OpGeq32U: {fn: foldGeqU},
	OpGeq64U: {fn: foldGeqU},
	OpGeq32F: {fn: foldGeq32F},
	OpGeq64F: {fn: foldGeq64F},

	OpAndB: {genFn: foldAndB},
	OpOrB:  {genFn: foldOrB},

	OpEqB:    {fn: foldEq},
	OpNeqB:   {fn: foldNeq},
	OpNot:    {fn: foldNot},
	OpNeg8:   {fn: foldNeg},
	OpNeg16:  {fn: foldNeg},
	OpNeg32:  {fn: foldNeg},
	OpNeg64:  {fn: foldNeg},
	OpNeg32F: {fn: foldNeg32F},
	OpNeg64F: {fn: foldNeg64F},
	OpCom8:   {fn: foldCom},
	OpCom16:  {fn: foldCom},
	OpCom32:  {fn: foldCom},
	OpCom64:  {fn: foldCom},
	// OpCtz32 TODO
	// OpCtz64
	// OpBswap32
	// OpBswap64
	// OpSqrt

	// OpPhi
	OpCopy: {fn: foldCopy},

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

	OpSignExt8to16:  {fn: foldSignExt8},
	OpSignExt8to32:  {fn: foldSignExt8},
	OpSignExt8to64:  {fn: foldSignExt8},
	OpSignExt16to32: {fn: foldSignExt16},
	OpSignExt16to64: {fn: foldSignExt16},
	OpSignExt32to64: {fn: foldSignExt32},
	OpZeroExt8to16:  {fn: foldZeroExt8},
	OpZeroExt8to32:  {fn: foldZeroExt8},
	OpZeroExt8to64:  {fn: foldZeroExt8},
	OpZeroExt16to32: {fn: foldZeroExt16},
	OpZeroExt16to64: {fn: foldZeroExt16},
	OpZeroExt32to64: {fn: foldZeroExt32},
	OpTrunc16to8:    {fn: foldCopy}, // XXX
	OpTrunc32to8:    {fn: foldCopy},
	OpTrunc32to16:   {fn: foldCopy},
	OpTrunc64to8:    {fn: foldCopy},
	OpTrunc64to16:   {fn: foldCopy},
	OpTrunc64to32:   {fn: foldCopy},

	OpCvt32to32F: {fn: foldCvt32to32F},
	OpCvt32to64F: {fn: foldCvt32to64F},

	OpCvt64to32F: {fn: foldCvt64to32F},
	OpCvt64to64F: {fn: foldCvt64to64F},

	OpCvt32Fto32: {fn: foldCvt32Fto32},
	OpCvt32Fto64: {fn: foldCvt32Fto64},

	OpCvt64Fto32: {fn: foldCvt64Fto32},
	OpCvt64Fto64: {fn: foldCvt64Fto64},

	OpCvt32Fto64F: {fn: foldCvt32Fto32},
	OpCvt64Fto32F: {fn: foldCvt32Fto32},

	// OpIsNonNil NOPE-NOPE-NOPE
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

	OpCvt32Uto32F: {fn: foldCvt32Uto32F},
	OpCvt32Uto64F: {fn: foldCvt32Uto64F},

	OpCvt32Fto32U: {fn: foldCvt32Fto32U},
	OpCvt64Fto32U: {fn: foldCvt64Fto32U},
	OpCvt64Uto32F: {fn: foldCvt64Uto32F},
	OpCvt64Uto64F: {fn: foldCvt64Uto64F},
	OpCvt32Fto64U: {fn: foldCvt32Fto64U},
	OpCvt64Fto64U: {fn: foldCvt64Fto64U},

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
