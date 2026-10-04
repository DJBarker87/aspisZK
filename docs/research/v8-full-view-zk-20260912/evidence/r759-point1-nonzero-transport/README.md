# R759 point-1 nonzero transport-leaf emitter — review prototype

This source-only stdlib Rust emitter is not compiled or run. It consumes the
pinned R748 leaf plan and the seven already-green R753 basis source chunks.
It filters the 196 records whose point-1 source basis is nonzero, verifies the
basis source hashes and their 196 exact index/value declarations, then emits
seven chunks of at most 32 named transport leaves.

Each emitted proof names `j`, proves `order j = original` by `decide`, rewrites
with the exact R753 `point1_basis_original` lemma, invokes the canonical R755
`w_from_basis`, and proves the transport branch through `mem_erase`, the T163
filter, and the literal `isInactive` Boolean. It retains the expression
`basis + 576` for inactive records; it performs no new field arithmetic.

The shared pivot is not generated: R755 already uses R754's proved pivot basis.
The emitter has `--emit` (refuses output overwrite) and byte-exact `--check`
from the same renderer. No source chord, point observation, rank, or native
semantics is evaluated or claimed.
