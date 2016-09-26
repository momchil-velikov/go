### Improvements to basic block trimming

Basic block trimming is improved to:
 - trim blocks with multiple predecessors
 - trim blocks, which contain only φ-functions
 - trim blocks, which can be merged into the successor block

As an example, compiling the following source:

```go
    package p

    type Node struct {
            Key         int
            Left, Right *Node
    }

    func Search(r *Node, k int) *Node {
            for r != nil {
                    switch {
                    case k == r.Key:
                            return r
                    case k < r.Key:
                            r = r.Left
                    default:
                            r = r.Right
                    }
            }
            return nil
    }
```
 with `GOSSAFUNC=Search go tool compile t.go`, results in the following code:

          00000 (t.go:8)	TEXT	"".Search(SB), $0
          00001 (t.go:8)	FUNCDATA	$0, "".gcargs·0(SB)
          00002 (t.go:8)	FUNCDATA	$1, "".gclocals·1(SB)
          00003 (t.go:8)	TYPE	"".r(FP)type.*"".Node, $8
          00004 (t.go:8)	TYPE	"".k+8(FP)type.int, $8
          00005 (t.go:8)	TYPE	"".~r2+16(FP)type.*"".Node, $8
    v40   00006 (t.go:9)	MOVQ	"".k+8(FP), AX
    v34   00007 (t.go:9)	MOVQ	"".r(FP), CX
    v33   00008 (t.go:9)	TESTQ	CX, CX
    b2    00009 (t.go:9)	JEQ	$0, 22
    v16   00010 (t.go:11)	MOVQ	(CX), DX
    v21   00011 (t.go:11)	CMPQ	DX, AX
    b9    00012 (t.go:11)	JEQ	$0, 19
    v64   00013 (t.go:13)	CMPQ	AX, DX
    b13   00014 (t.go:13)	JGE	17
    v36   00015 (t.go:14)	MOVQ	8(CX), CX
    b4    00016 (t.go:9)	JMP	8                  <---+
    v42   00017 (t.go:16)	MOVQ	16(CX), CX         |
    b21   00018 (t.go:10)	JMP	16                 ----+
    v28   00019 (t.go:12)	VARDEF	"".~r2+16(FP)
    v29   00020 (t.go:12)	MOVQ	CX, "".~r2+16(FP)
    b10   00021 (t.go:12)	RET
    v44   00022 (t.go:19)	VARDEF	"".~r2+16(FP)
    v45   00023 (t.go:19)	MOVQ	$0, "".~r2+16(FP)
    b5    00024 (t.go:19)	RET
    00025 (<unknown line number>)	END

Note the jump at 18 jumps to another jump at 16.

Looking at the function after trimming:

    after trim [199 ns]

    b1:
    v1 = InitMem <mem>
    v2 = SP <uintptr> : SP
    v67 = Arg <*Node> {r} : r[*Node]
    v59 = Arg <int> {k} : k[int]
    v40 = LoadReg <int> v59 : AX
    v34 = LoadReg <*Node> v67 : CX
    Plain → b2

    b2: ← b1 b4
    v8 = Phi <*Node> v34 v68 : CX
    v33 = TESTQ <flags> v8 v8
    NE v33 → b9 b5 (likely)

    b9: ← b2
    v16 = MOVQload <int> v8 v1 : DX
    v21 = CMPQ <flags> v16 v40
    EQ v21 → b10 b13 (unlikely)

    b13: ← b9
    v64 = CMPQ <flags> v40 v16
    LT v64 → b19 b21

    b19: ← b13
    v36 = MOVQload <*Node> [8] v8 v1 : CX
    Plain → b4

    b4: ← b21 b19                       <
    v68 = Phi <*Node> v42 v36 : CX      <- no actual code
    Plain → b2                          <

    b21: ← b13
    v42 = MOVQload <*Node> [16] v8 v1 : CX
    Plain → b4

    b10: ← b9
    v28 = VarDef <mem> {~r2} v1
    v29 = MOVQstore <mem> {~r2} v2 v8 v28
    v30 = Copy <mem> v29
    Ret v30

    b5: ← b2
    v44 = VarDef <mem> {~r2} v1
    v45 = MOVQstoreconst <mem> {~r2} [val=0,off=0] v2 v44
    v47 = Copy <mem> v45
    Ret v47

  The jump at 16 corresponds to the edge `b21 -> b4`. The block `b4`
contains only φ-ops, i.e. no actual code besides the jump to
`b2`. However `b4` is not trimmed, because it a) has more than one
predecessor, and b) it is not empty.

This change enhances `trim.go` to remove more blocks, subject to the
following criteria:

- block has predecessors (i.e. not the start block)
- block is `BlockPlain`
- block does not loop back to itself
- block is the single predecessor of its successor; the instructions of
  the block are merged into the successor
- block does no emit actual code, besides a possible unconditional jump.
  Currently only `OpPhi` are considered to not be actual code, perhaps
  `OpKeepAlive`/others should be considered too?

When a φ is merged into the successor block, the number of its arguments
has to be adjusted to match the number of block predecessors. The
merge is done as follows:

* If the predecessor block contains `u = φ(u0, u1, ..., un)` and the
  successor block contains `v = φ(v0, v1, ..., u, ..., vk)`, then the
  merged φ is `v = φ(v0, v1, ..., u0, ..., vk, u1, ..., un)`;

* If the predecessor block contained `u = φ(u0, u1, ..., un)` and the
  successor block contains `v = φ(v0, v1, ..., vi, ..., vk)`, the φ does
  not use a value from the predecessor block, then the merged φ is `v =
  φ(v0, v1, ..., vk, vi, vi, ...)`;

* if the predecessor block contained a φ, which has no uses as an
  argument to φ-operations in the successor, then the number of
  arguments is just padded by replicating the first argument. This is
  not generally correct, but at this point of compilation, φ-operations
  are needed only for liveness analysis and do not generate code.

As for the example above, after the changes to `trim()`, the block `b4`
is trimmed and the jump at 18 jumps directly to 8.
