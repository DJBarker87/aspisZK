# R689 selected root exponent arithmetic

R689 proves integer and modular facts for the exponent function
`E(n) = 2^11 + 2^13*n` on `Fin (2^18)`. The exact Lean source is
[R689SelectedRootExponents.lean](lean/AspisV8R19/R689SelectedRootExponents.lean).

The focused target compiled successfully with Lean 4.32.0 in the pinned cached
workspace. The exact target was `.r21-scratch/R689SelectedRootExponents.lean`,
source SHA256 `17c36e529a3f42be8a898c4ce341f5a6479444c82fdf56df566119cecc07c3e4`,
at source revision `d8e684eea7fdcc4b8dd7fd45db08f5ee092edd2b`. It exited 0 in
1.08 seconds, used 1,873,128 KiB peak Lean-child RSS, and used no swap. The job
used `MemoryHigh=5G`, `MemoryMax=7G`, `MemorySwapMax=0`, `TasksMax=128`, and
Lean flags `-j1 -M4500`. The complete output, receipt, source snapshot, and
earlier attempts are retained in
[the evidence directory](evidence/r689-selected-root-exponents/).

The compiled declarations establish positivity and the strict `2^31` upper
bound, injectivity of `E`, nonzero residues in `ZMod (2^31)`, residue equality
only for equal indices, the strict bound `E(i)+E(j)<2^32`, the exact congruence
`(E(i)+E(j)) % 8192 = 4096`, and impossibility of opposite residues. Their
complete `#print axioms` reports contain only `propext`, `Classical.choice`,
and `Quot.sound` (the natural-number modular arithmetic lemmas require only
`propext` and `Quot.sound`).

This result is only exponent arithmetic. The separate R691 result establishes
the abstract norm-one generator order and the coset-root algebra. The first
remaining bridge is that the selected Rust table/window construction and its
`reverse18` query index produce exactly `E(q)` for every accepted query. The
source-indexed inventory is preserved in
[the R691 evidence directory](evidence/r691-circle-coset-roots/source-root-inventory.md).
The later R691 target successfully imported the exact cached R689 `.olean`;
that compile confirms the cache copy is usable, but does not enlarge R689's
theorem scope.

The attempt history is preserved. The first broad-import attempt exceeded
Lean's configured memory threshold; the subsequent focused attempts record the
missing tactic import and intermediate proof errors. A downstream R691 attempt
before cache placement failed because its expected canonical cache path was
absent. The exact R689 `.olean` was then copied byte-for-byte into the expected
cache location, and the later R691 compile succeeded.
