# R17 small-block certificate route

## Frozen source active projection

Base `212f6757` plus this changeset. The new
`evidence/r17-active-source-rows.json` contains the actual source's ascending
214 active original row IDs and, in exactly that order, their coefficient
indices under the immutable transport. The source test computes the
inverse-permutation indices directly from `transport().order`, rejects
the balancing pivot for every active row, and requires an exact artifact
match. This disambiguates the block records' `rows`: those positions now
index an explicit source coefficient list, rather than an implicit ordering.

The generator preflight requires the projection artifact, checks 214
distinct indices, original row order and pivot exclusion, and coefficient
bounds 100..1018. `--check` passes and the generated determinant leaves
are byte-for-byte unchanged; they were not recompiled. The remaining
formal binding must use these indices to instantiate the sparse unit-column
source model and prove the block values/structural zeros, then apply the
composition gates. The new artifact is source-checked data, not an
extracted Rust semantics proof or a privacy/soundness result.

Focused command: `/usr/bin/time -l cargo test --offline --locked --release
--jobs 1 -p aspis-prover --lib r17_active_minor_polynomial_witness
-- --nocapture`, in the privacy worktree. Export pass: exit 0, 24.74s,
peak RSS 568147968 bytes, swaps 0. Final frozen-projection check: exit 0,
24.05s, peak RSS 567853056 bytes, swaps 0. Both pass one test, retaining
the full-minor, small-block and entry-correspondence checks. Logs:
`/tmp/aspis-r15-host.drHYn9/r17-active-source-rows.log` and
`/tmp/aspis-r15-host.drHYn9/r17-active-source-rows-frozen.log`.
No Lean source changed, so no new axioms audit or full replay was run.

## Compiled lightweight composition gates

Base `4d617337` plus this changeset. `BlockComposition.lean` proves:
an upper two-block matrix with nonzero diagonal determinants has nonzero
determinant; a row-permuted nonzero determinant implies the original is
nonzero; and a nonzero determinant after a ring homomorphism implies the
original determinant is nonzero. The last applies to polynomial evaluation.
The two-block theorem can compose a balanced recursive block certificate
without expanding any dense determinant. All premises remain explicit.

The first attempted general BlockTriangular import exceeded the 1800 MB
Lean allocation cap before producing a declaration result. Instead of
raising the cap or rerunning it unchanged, the proof was changed to use
the lighter determinant module's named two-block formula. This route
compiles below the same cap. No source-specific zero-pattern or 133-block
identification is claimed from these generic gates; that remains the next
certificate proposition.

Focused command from `/Users/dominic/ZK/AspisFormal`:
`/usr/bin/time -l lake env lean -j1 -M1800 /Users/dominic/ZK/.worktrees/ZK-v8-privacy-repair-20260913/docs/research/v8-full-view-zk-20260912/lean/AspisV8R17/BlockComposition.lean`.

| Attempt | Exit | Wall seconds | Peak RSS bytes | Swaps |
| --- | ---: | ---: | ---: | ---: |
| Broad block import, allocation cap | 134 | 9.19 | 1892122624 | 0 |
| Lightweight two-block/permutation gates | 0 | 9.98 | 1731575808 | 0 |
| Map bridge, map/mapMatrix rewrite mismatch | 1 | 3.70 | 1739653120 | 0 |
| Final ring-homomorphism mapMatrix bridge | 0 | 4.45 | 1739472896 | 0 |

All three final axioms audits use only propext, Classical.choice,
Quot.sound. The failed bridge's sorryAx audit is rejected. Two harmless
unused-IsDomain section-variable warnings remain. Outputs are in the
command-tool record. No Rust source changed and no unchanged runtime
regression or full formal manifest was replayed.

## Compiled tiny determinant leaves

Base `b1ad6787` plus this changeset. `tools/r17_block_determinants.py`
validates all 133 frozen records, verifies complete row/column coverage,
checks canonical residue ranges and dimensions, deduplicates the 29
matrices, and emits `lean/AspisV8R17/BlockDeterminants.lean` with an input
SHA256. `--check` compares the entire regenerated file exactly; it passes.

All 29 named `blockN_det_ne_zero` theorems compile over ZMod 2147483647.
The generator explicitly applies `Matrix.det_fin_one`, `det_fin_two` or
`det_fin_three`, then kernel-checks only the resulting tiny arithmetic
expression. No 214-square determinant, inverse or recurrence is reduced.
The largest case has at most six products of three 31-bit residues; there
is no large reduction graph hidden in these leaves. No native_decide or
new axiom is used. Each final axioms audit is exactly propext,
Classical.choice, Quot.sound.

These prove nonzero determinants of the frozen evaluated matrices only.
The first remaining formal proposition is that the permuted source-model
minor is block triangular with diagonal blocks given by these matrices
(with their 133-record reuse), followed by determinant composition. The
source executable checks are not substituted for that formal connection.
Probability accounting and full privacy/soundness remain separate.

Focused preflight: `python3 docs/research/v8-full-view-zk-20260912/tools/r17_block_determinants.py --check`
from the privacy worktree reports blocks=133, unique=29, max_dimension=3,
match=true. The generator writes to stdout; source edits used apply_patch.

Lean command from `/Users/dominic/ZK/AspisFormal`:
`/usr/bin/time -l lake env lean -j1 -M1800 /Users/dominic/ZK/.worktrees/ZK-v8-privacy-repair-20260913/docs/research/v8-full-view-zk-20260912/lean/AspisV8R17/BlockDeterminants.lean`.
Initial norm_num-based proofs left modular and matrix-entry goals: exit 1,
wall 12.07s, peak RSS 1756856320 bytes, swaps 0. Their sorryAx audits are
rejected. The generator was changed to the named determinant formula plus
small direct decision proof, and its check reran successfully. Final
compile: exit 0, wall 7.71s, peak RSS 1746747392 bytes, swaps 0.
All 29 final audits pass. Output is in the command-tool record. No Rust
source changed, and no unchanged runtime or full manifest was rerun.

## Frozen block artifact

Base `00cc7a1e` plus this changeset. The source test now asserts exact
equality with `evidence/r17-minor-blocks.jsonl`, containing all 133 blocks.
Each record gives reachable-set `order`, `rows` as zero-based positions
in the original 214-active-row list, `columns` as zero-based positions
in the frozen 214-column minor, and `values` in row-major order. Values
are canonical M31 residues at alpha=2,u=3,v=4; each value is checked to
embed back into QM31 exactly, excluding a silently discarded extension
component. Columns refer to `r17-active-minor-columns.txt`, not directly
to the 699-column map. Sorting blocks by decreasing order gives the
checked triangular order. Equal-order distinct blocks have no connecting
support edge.

The 133 records contain 29 distinct evaluated matrices, allowing repeated
tiny determinant proofs to share named lemmas. This is frozen exact source
evidence, not yet a generated Lean certificate. Next: compile determinant
nonzero leaves for those 29 cases and formally bind their reuse and the
block permutation/structural zero pattern. A nonzero determinant at this
algebraic witness remains distinct from a source-sampler probability law.

Focused command is the same named offline/locked/release/jobs=1 test below.
Initial export compilation failed on a field-member typo and JSON format
brace: exit 101, 2.52s, RSS 416792576 bytes. Correcting the member left
the format error: exit 101, 1.81s, RSS 404979712 bytes. Both were fixed.
Export test then passed: exit 0, 23.85s, RSS 566951936 bytes. All zero
swaps. Logs under `/tmp/aspis-r15-host.drHYn9/` are
`r17-minor-block-data.log`, `r17-minor-block-data-v2.log` and
`r17-minor-block-data-v3.log`. The artifact was populated from the passing
output, then added as an exact assertion to the source test.
Final frozen-artifact assertion passed: exit 0, 24.43s, RSS 566099968
bytes, zero swaps; `r17-minor-block-frozen.log` in the same log directory.

Base `c54fedc8` plus this changeset, 2026-09-21.

The fixed 214-column minor has only 599 potentially nonzero polynomial
entries under the six-constant representation. The support calculation
uses whether ANY of the six field constants is nonzero. It does not use
entries that happen to vanish at alpha=2,u=3,v=4. This is an overapproximate
symbolic support, so additional polynomial cancellations cannot invalidate
its zero pattern.

A perfect matching of this support identifies rows with columns. Mutual
reachability partitions the resulting directed graph into diagonal blocks.
The test checks that every edge between different blocks strictly decreases
reachable-set cardinality, yielding a block-triangular order. It separately
checks each diagonal block at the fixed evaluation using the existing
independent inverse-product rank check. The expected partition is 60
one-by-one, 65 two-by-two and 8 three-by-three blocks, totaling 214.

This changes the planned formal certificate: use the block permutation,
structural zeros and 133 tiny determinant witnesses, not a dense 214-square
inverse or expansion. No generated Lean certificate or formal determinant
factorization is claimed yet. The next required artifact is a frozen block
layout and source-bound small-block coefficient certificate, then generic
block-triangular determinant composition. This is a resource preflight and
exact executable certificate analysis, not a full privacy or soundness
result. All source/adaptive/shared-oracle/retry/publication obligations
remain separate.

## Focused evidence

Command from the privacy worktree: `/usr/bin/time -l cargo test --offline
--locked --release --jobs 1 -p aspis-prover --lib
r17_active_minor_polynomial_witness -- --nocapture`.
Initial support decomposition passed: exit 0, wall 24.74s, peak RSS
566640640 bytes, zero swaps. Log:
`/tmp/aspis-r15-host.drHYn9/r17-minor-support.log`.
The existing full minor rank, fixed pivot list and 149586 entry comparisons
remain checked. No Lean source changed or axioms audit ran in this step.
The strengthened test checking the exact block histogram, strict triangular
ordering and every diagonal block passed: exit 0, wall 24.41s, peak RSS
568066048 bytes, zero swaps; log
`/tmp/aspis-r15-host.drHYn9/r17-minor-blocks.log`.
