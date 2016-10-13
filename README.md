## The Go Programming Language

This repository contains experimental/unstable changes to the Go
compiler SSA backend

(original [README.md](https://github.com/momchil-velikov/go/blob/master/README.md))
### Development branches

* dev.chill: This README.md
* dev.chill.trim: improvements the the basic block trimming pass ([README.md](https://github.com/momchil-velikov/go/blob/dev.chill.trim/README.md))
  - merged upstream [be302e6](https://github.com/golang/go/commit/be302e6d43790c3398e5b03c955f257868855a80)
* dev.chill.gvn-hoist: GVN code hoisting pass ([README.md](https://github.com/momchil-velikov/go/blob/dev.chill.gvn-hoist/README.md)) 
* dev.chill.licm: Loop Invariant Code Motion pass ([README.md](https://github.com/momchil-velikov/go/blob/dev.chill.licm/README.md)) 
* dev.chill.loop-inv: Loop Inversion ([README.md](https://github.com/momchil-velikov/go/blob/dev.chill.loop-inv/README.md))
* dev.chill.sccp: Sparse Conditional Constant Propagation pass ([README.md](https://github.com/momchil-velikov/go/blob/dev.chill.sccp/README.md))

Note that the `dev.chill.*` branches are often rebased onto `master`.
