### GVN value hoisting

  This pass attempts to find expressions with identical values and move
them to a common point, where they are evaluated only once.

  The pass works as a subroutine of `cse()`. The CSE in the Go compiler
is done via global value numbering based on splitting `Value`s into
equivalence classes. Within each equivalence class, the CSE replaces
uses of `Value` `u` by a use of `v` where `v` dominates `u`. After the
CSE, the equivalence classes are left with a set of `Value`s, such that
neither one dominates the others.

  Then we choose basic blocks, where to move the remaining computations.

  The choice of basic blocks must be safe, in the sense that we should not
add a computation that wouldn't be performed in the unoptimized
program. For this, we compute a variant of anticipated expressions
data-flow analysis, which gives at each block the set of expressions,
definitely evaluated on any path, starting from the block. Each
expression in the set is represented by the ID of the equivalence class
of the expression's `Value`. Unlike the classic anticipated expressions
analysis, we do not yet consider the availability of the expression
operands at each point, as it may change as a result of our own
transformations.

  The other aspect of safety is dominance: we may move a computation
only to a block, that dominates the original computation, in order to
preserve the invariant that SSA definitions dominate their uses.

  In order to reduce code size, we should replace two or more
computations with one, therefore a candidate block should be a common
dominator. In the same time, we should not move the computations too far
ahead in the program, as this would increase lifetimes and register
pressure. For this, we place the restriction that each candidate block
must be a parent to a block, containing an original computation.

  The choice of blocks proceeds as follows. For each `Value` in an
equivalence class, which is defined in a block with a single parent, we
check if the corresponding expression is anticipated at the parent; we
collect all such parents in a set and eliminate all blocks, dominated by
another block in the set.  Then all the `Value`s in the equivalence
class are assigned to their dominating blocks.

  The hoisting works class-by-class, in such an order that definitions
are hoisted before their uses. Within a a class, for each `Value`, we
check whether each operand has a `Value` of the same equivalence class
that is available at the hoist destination block; we may rewrite the
`Value` to use a different operand as a consequence of this check.  This
concludes the final check for legality of the code motion: the
expression is anticipated at the destination block, the destination
dominates the original block and the operands are available at the
destination (perhaps after hoisting them). Therefore, we create a new
`Value` at the destination and change the current `Value` to be a copy.
