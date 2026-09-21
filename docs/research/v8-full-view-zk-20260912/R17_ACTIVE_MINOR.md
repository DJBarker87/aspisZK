# Fixed active-minor nonvanishing witness

## Assembled weighted scatter and transport

Base `1bc073f1` plus this changeset. `WeightedScatter.lean` defines the
full edge list by concatenating each concrete weighted column schedule.
It proves every input/output bound from `weighted_schedule_bounds` and
instantiates the finite chord identity at lengths 512/513 with no remaining
edge-bound premise. `sourceChord_six_constants` therefore covers the
assembled index, weight, scatter, parity and finite-read model.

`active_transport_six_constants` composes this with the retained R16
inverseTransport definition at any non-pivot row, using its fixed
inverse-permutation index. The non-pivot premise remains explicit. Actual
source active rows are non-pivot (the pivot is inactive), but the fixed
Rust permutation is not represented by an extracted semantics artifact
in this theorem. Similarly abstract half and field operations still need
the stated source representation correspondence. The immediate next
algebraic bridge is polynomial evaluation of these assembled six constants
and the fixed-minor certificate; source field/word correctness and adaptive
sampler probability remain distinct open obligations.

## This step's focused evidence

The two newly imported prerequisite oleans were missing, so they were
built in the retained cache; this was not a full manifest replay. Commands
ran from `/Users/dominic/ZK/AspisFormal` under `/usr/bin/time -l lake env`,
with Lean `-j1 -M1800`. The source root is the worktree's
`docs/research/v8-full-view-zk-20260912/lean`; outputs are under
`target/r17-lean/AspisV8R17/{IndexSchedule,SourceScatter}.olean`.
The successful prerequisite commands use `-R SOURCE_ROOT -o OUTPUT FILE`.
The bridge command sets LEAN_PATH to worktree target/r17-lean and
target/r16-lean ahead of the existing path, then invokes Lean on
`SOURCE_ROOT/AspisV8R17/WeightedScatter.lean`.

| Target/attempt | Exit | Wall seconds | Peak RSS bytes | Swaps |
| --- | ---: | ---: | ---: | ---: |
| IndexSchedule olean, missing -R | 1 | 3.69 | 669876224 | 0 |
| SourceScatter olean, missing -R | 1 | 0.70 | 669728768 | 0 |
| WeightedScatter, missing prerequisite object | 1 | 1.10 | 669745152 | 0 |
| IndexSchedule olean with source root | 0 | 5.86 | 1319665664 | 0 |
| SourceScatter olean with source root | 0 | 2.40 | 1383022592 | 0 |
| WeightedScatter/chord composition | 0 | 1.59 | 1340866560 | 0 |
| Final active transport composition | 0 | 3.70 | 1383038976 | 0 |

All successful axioms audits use only propext, Classical.choice and
Quot.sound (subsets as printed); no sorryAx. Outputs are in the command
tool record. No Rust or production paths changed; no runtime replay.

## Weighted schedule correspondence

Base `2f915390` plus this changeset. `IndexSchedule.lean` adds a weighted
version of the same loop with `nextScale=scale*half`, in the source order.
`weightedIndexLoop_powers` proves for every fuel, row and bit, over any
monoid, that starting at half^bit produces exactly the index-loop edge
list with each exponent replaced by that power. The proof is structural
induction, not evaluation over sample field elements.

`weighted_schedule_bounds` combines this identity with the checked
schedule: for every j<n where scheduleBounded n is certified, the loop
started at scale one succeeds, all output indices are below n+1, and
every weight is half^k for k<=9. The retained certificates discharge its
schedule premise at n=512 and n=513. No nonzero, randomness or new hiding
premise is needed for this loop identity.

Next is to assemble the indexed weighted edges into the scatter/chord
model and instantiate the active transport projection, then connect the
polynomial evaluation and nonzero-minor certificate. This abstract algebra
does not silently assert correctness of Rust's M31/QM31 representation,
its embedding or machine-word operations. Full privacy/soundness and
source adaptive probability accounting remain open.

Focused command from `/Users/dominic/ZK/AspisFormal`:
`/usr/bin/time -l lake env lean -j1 -M1800 /Users/dominic/ZK/.worktrees/ZK-v8-privacy-repair-20260913/docs/research/v8-full-view-zk-20260912/lean/AspisV8R17/IndexSchedule.lean`.
Weighted-loop identity pass: exit 0, 6.43s, peak RSS 1303429120 bytes,
zero swaps. Final combined bounds pass: exit 0, 3.32s, peak RSS
1305296896 bytes, zero swaps. New axioms audits: the identity uses only
propext; the combined bounds use propext and Quot.sound. No sorryAx.
Outputs are in the command-tool record. No Rust source changed and no
unchanged runtime/full suite was rerun.

## Concrete bit-index bounds

Base `7f0ee60a` plus this changeset. `IndexSchedule.lean` implements
the index-only source loop: test the current bit, clear it by XOR when
set, emit the new row with incremented half-power exponent, and finally
emit the row OR current bit. Ten fuel units are used. The two concrete
certificates prove success for every input column at lengths 512 and 513,
with targets respectively below 513 and 514 and weight exponents <=9.
`scheduleBounded_sound` proves the 16-column block checker covers every
j<n by division/remainder; the final theorems expose existential successful
edge lists and per-edge bounds, not merely Boolean test results.

The source loop has at most nine cleared low bits at these lengths.
Its finite certificates contain about a thousand edges, not a large
field recurrence. An initial flat List.range traversal hit Lean's recursion
depth limit; the certificate was reshaped into 16-column blocks instead
of raising depth, heartbeat or memory limits. Native evaluation and
native_decide were not used. These kernel checks depend only on propext
(concrete Booleans) and propext/Quot.sound (coverage and bound theorems).

Remaining correspondence: connect the schedule's half-power exponents
to field weights and the source scatter execution, assemble the fixed
active inverse permutation, and connect polynomial evaluation/nonzero
minor evidence. The Nat index model is not by itself a Rust machine-word
or field implementation proof. No adaptive sampler/security claim follows.

Focused command from cached `/Users/dominic/ZK/AspisFormal`:
`/usr/bin/time -l lake env lean -j1 -M1800 /Users/dominic/ZK/.worktrees/ZK-v8-privacy-repair-20260913/docs/research/v8-full-view-zk-20260912/lean/AspisV8R17/IndexSchedule.lean`.

| Attempt | Exit | Wall seconds | Peak RSS bytes | Swaps |
| --- | ---: | ---: | ---: | ---: |
| Flat traversal, recursion-depth failure | 1 | 4.39 | 1241956352 | 0 |
| Blocked finite certificates | 0 | 8.38 | 1294286848 | 0 |
| Coverage theorem branch equality mismatch | 1 | 5.47 | 1301692416 | 0 |
| Final coverage and both universal bounds | 0 | 2.31 | 1300512768 | 0 |

Failed audits with sorryAx are rejected; all five final audits exclude it.
Outputs are in the command-tool record. No Rust change or unchanged full
regression replay occurred.

## Finite-length composition

Base `7242aeb8` plus this changeset. `SourceScatter.lean` now defines
`finiteChordEven`/`finiteChordOdd` with explicit zero-extended length-n
parity vectors, length-(n+1) first scatter outputs and length-(n+2)
second scatter output. Their equivalence to the unbounded chord model
is proved under explicit output-edge bounds. The interleaved
`finiteChordCoefficient_eq` combines both branches, and
`finite_source_six_constants` proves the full six-constant identity on
these finite-length reads. Specializing n=512 matches the 512/513/514
intermediate lengths inspected in `chord_product`.

This closes the intermediate-padding composition within the source-shaped
model, not an automatic extraction of Rust. The first remaining concrete
correspondence obligation is the index-only bit schedule and fixed
transport instantiation (including active rows not being the balancing
pivot), followed by the polynomial evaluation bridge and kernel-checked
nonzero certificate. Field implementation correctness, high-tail
acceptance, sampler probability, and global privacy/soundness remain
separate. The existing 1025 basis tests are not silently promoted into a
full Rust refinement theorem.

Cached focused command in `/Users/dominic/ZK/AspisFormal`:
`/usr/bin/time -l lake env lean -j1 -M1800 /Users/dominic/ZK/.worktrees/ZK-v8-privacy-repair-20260913/docs/research/v8-full-view-zk-20260912/lean/AspisV8R17/SourceScatter.lean`.
The even/odd finite equality pass exited 0 in 4.24s, peak RSS 1365295104
bytes. Final interleaved/six-constant pass exited 0 in 5.21s, peak RSS
1365065728 bytes. Both had zero swaps. All four new axioms audits list
only propext, Classical.choice, Quot.sound; no sorryAx. Outputs are in
the command-tool record. No Rust change or unchanged full replay.

## Zero-extension boundary lemmas

Base `877fcba3` plus this changeset. `SourceScatter.lean` now proves:
zero extension preserves linear combinations; input padding is invisible
to an edge list whose input indices are in bounds; bounded output edges
produce zero above their bound; output padding is then the identity;
splitting a length-2n input by either parity agrees with zero extending
the length-n split; and truncation preserves every retained coefficient.
All results quantify over arbitrary values and lengths. Bounds remain
explicit hypotheses, with the relevant concrete schedules already checked
at lengths 512 and 513 by the retained source-basis test.

These lemmas remove the padding algebra obstacle to composing the source
get-or-zero reads with the chord model. They do not waive the separate
assertion that the high four output coefficients vanish: preserving a
retained prefix does not prove acceptance of an arbitrary input. Concrete
array/edge/transport instantiation, polynomial evaluation and the field
implementation correspondence remain to be assembled. No sampler law,
global privacy or soundness gate is closed by padding identities.

Focused cached command in `/Users/dominic/ZK/AspisFormal`:
`/usr/bin/time -l lake env lean -j1 -M1800 /Users/dominic/ZK/.worktrees/ZK-v8-privacy-repair-20260913/docs/research/v8-full-view-zk-20260912/lean/AspisV8R17/SourceScatter.lean`.
Initial four boundary lemmas: exit 0, wall 4.42s, peak RSS 1358430208
bytes, zero swaps. Final file with parity and retained-index lemmas:
exit 0, wall 1.98s, peak RSS 1360691200 bytes, zero swaps. Final
`#print axioms` outputs contain only propext, Quot.sound and (for the
parity arithmetic proof) Classical.choice. No sorryAx. Outputs are in the
command-tool record. No Rust changes or unchanged full regressions.

## Composed source-shaped chord theorem

Base `330170d1` plus this changeset. `SourceScatter.lean` now defines
the exact algebraic even/odd formulas used by `chord_product`, including
the second scatter application in the even coefficient. It proves each
formula linear in the input, decomposes it into its three chord basis
components, and interleaves the two formulas by coefficient parity.
`active_source_six_constants` proves for every edge schedule, every
input pair q,s, scalar t, chord a,b,c and selected index r that the
coefficient on q-t*s equals the corresponding six-constant expression.
Thus the linear-map premise is discharged for this explicit source-shaped
model; it is no longer merely an abstract assumed linear functional.

This theorem selects any coefficient, permitting the active row's fixed
inverse-permutation index. It does not itself prove the concrete Rust
array-to-function representation, zero extension beyond vector lengths,
the index schedule refinement, or the immutable transport permutation.
Those source representation obligations and polynomial evaluation are the
next bridge; existing exhaustive basis checks remain executable evidence,
not an extracted semantics theorem. The assertion/truncation of the high
four coefficients also remains distinct from this pre-truncation algebra.
No probability, privacy, or malicious-prover soundness claim is added.

Focused command in `/Users/dominic/ZK/AspisFormal` remained
`/usr/bin/time -l lake env lean -j1 -M1800 /Users/dominic/ZK/.worktrees/ZK-v8-privacy-repair-20260913/docs/research/v8-full-view-zk-20260912/lean/AspisV8R17/SourceScatter.lean`.
Initial nested-scatter rewrite failed: exit 1, 8.58s, RSS 1355939840
bytes; its sorryAx audit is rejected. An explicit function-extensionality
rewrite fixed the nesting: exit 0, 1.77s, RSS 1353285632 bytes. After
adding parity composition and the six-constant theorem, final exit 0,
2.88s, RSS 1355988992 bytes. Every run had zero swaps. All final audits
use only propext and, where needed, Quot.sound; no sorryAx or new axiom.
Outputs are in the command-tool record. No Rust source changed, so no
unchanged runtime suite was repeated.

## Source-shaped scatter linearity

Base `289ddc7a` plus this changeset. `SourceScatter.lean` models the
ordered updates `out[row] += weight * input[column]`. For every finite
edge list it proves that the final accumulator is its initial value plus
the explicit coefficient sum, and that this sum preserves arbitrary
two-term linear combinations. The edge list may have repeated targets;
no sparsity, disjointness, random sampling or nonzero premise is needed.

In `r16_final_posterior.rs::times_x`, source inspection identifies exactly
these updates. Their columns, rows and M31 weights depend only on the
input length and public loop indices, never input coefficients. The new
`r17_times_x_scatter_basis_correspondence` records that fixed edge schedule
and checks every standard basis vector against the existing source
routine. Length 512 has 1023 edges and output length 513; length 513 has
1024 edges and output length 514. All 1025 basis checks pass and all
edge indices are checked in bounds. These are precisely the two input
lengths used in chord multiplication, including its second x application.

This proves the generic loop algebra and checks the complete finite basis
correspondence. It does not claim an extracted Rust semantics theorem.
The next composition obligation is to combine the scatter maps, parity
split/interleave, fixed chord components and active inverse-permutation
projection into the already proved six-constant identity, with explicit
source index correspondence and polynomial evaluation. Source field
arithmetic refinement and the nonzero-minor certificate remain separate
from a sampler probability law and global security obligations.

Lean command from `/Users/dominic/ZK/AspisFormal`:
`/usr/bin/time -l lake env lean -j1 -M1800 /Users/dominic/ZK/.worktrees/ZK-v8-privacy-repair-20260913/docs/research/v8-full-view-zk-20260912/lean/AspisV8R17/SourceScatter.lean`.
Exit 0, wall 8.22s, peak RSS 1347993600 bytes, swaps 0.
`scatter_run_value` uses only propext; `scatter_value_linear` uses propext
and Quot.sound. No sorryAx. Output is in the command-tool record.

Rust command: `/usr/bin/time -l cargo test --offline --locked --release
--jobs 1 -p aspis-prover --lib r17_times_x_scatter_basis_correspondence
-- --nocapture`. Exit 0, one test passed, wall 24.00s, peak RSS 564051968
bytes, swaps 0. Log: `/tmp/aspis-r15-host.drHYn9/r17-scatter-basis.log`.
No production source or negative regression changed; no unchanged full
suite or manifest was rerun.

## Six source coefficients and linearity bridge

Base `fa7dac80` plus this changeset. The fixed-witness Rust test now
computes the six constants for every active entry by applying each of
the three chord basis maps to the channel unit and the A unit, followed
by the source inverse transport. These constants do not use alpha,u,v.
It reconstructs all 214*699=149586 entries using the polynomial normal
form, checks equality with direct source computation at alpha=2,u=3,v=4,
then verifies the same frozen minor on the reconstructed matrix.

`ActiveLinearForm.lean` proves the six-constant identity universally for
three fixed linear functionals, and constructs a linear functional from
any finite coefficient vector. Source inspection confirms inverse
transport is a permutation except at the inactive pivot, so active rows
only require the corresponding coefficient projection. The remaining
compiled source bridge is the identification of the implemented
`times_x`/chord maps with those fixed finite coefficient functionals
(including their index rules), then composition with the polynomial
evaluation theorem. This identity is not asserted merely from the
single-point exhaustive entry check. No sampler or security gate is closed.

Focused Rust command: `/usr/bin/time -l cargo test --offline --locked
--release --jobs 1 -p aspis-prover --lib r17_active_minor_polynomial_witness
-- --nocapture`. Exit 0, one test passed, wall 24.20s, peak RSS 563953664
bytes, zero swaps; log `/tmp/aspis-r15-host.drHYn9/r17-active-entry.log`.

Focused Lean command in `/Users/dominic/ZK/AspisFormal`:
`/usr/bin/time -l lake env lean -j1 -M1800 /Users/dominic/ZK/.worktrees/ZK-v8-privacy-repair-20260913/docs/research/v8-full-view-zk-20260912/lean/AspisV8R17/ActiveLinearForm.lean`.
First attempt used an unavailable legacy import: exit 1, 0.95s,
669696000 bytes RSS. After using the cached module paths, Field was not
imported: exit 1, 5.04s, 1388609536 bytes. The theorem only requires a
commutative ring, so that existing general interface replaced Field.
Final compile: exit 0, 1.57s, 1399685120 bytes. Every attempt had zero
swaps. Final axioms: active_linear_form uses propext, Classical.choice,
Quot.sound; coefficientForm uses propext, Quot.sound. No accepted sorryAx.
No production paths or negative regressions changed; no full replay ran.

## Compiled entry normal form

On base `6d72748f` plus this changeset, `ActiveEntry.lean` defines the
normalized chord as multivariate polynomials in alpha,u,v and the entry
normal form `sum_j chord_j * (a_j - alpha^k*b_j)`, for six arbitrary
field constants a_j,b_j. It proves chord degree <=2 and entry total degree
<=5 whenever k<=3. This is the intended form because the quotient column
is one channel unit minus alpha^k times its A-channel unit, while chord
multiplication and inverse transport are linear in those coefficients.
The six constants must still be instantiated with the fixed source
basis maps, with a compiled correspondence theorem; that is the next
source-specific obligation. Per-variable entry bounds also remain to be
formalized. No source probability law is inferred from this algebra.

Focused command from the cached `/Users/dominic/ZK/AspisFormal` workspace:
`/usr/bin/time -l lake env lean -j1 -M1800 /Users/dominic/ZK/.worktrees/ZK-v8-privacy-repair-20260913/docs/research/v8-full-view-zk-20260912/lean/AspisV8R17/ActiveEntry.lean`.
The development attempts, all zero swaps, were:

| Attempt | Exit | Wall seconds | Peak RSS bytes |
| --- | ---: | ---: | ---: |
| Unavailable Omega import | 1 | 1.25 | 669499392 |
| Vector notation/noncomputability errors | 1 | 4.70 | 1670529024 |
| Concrete finite-case elaboration timeout and missing section end | 1 | 7.85 | 1670365184 |
| Symbolic conditional branches, explicit polynomial types | 0 | 1.76 | 1664729088 |

The failed finite-case elaboration was replaced rather than given a larger
heartbeat or memory cap. Both final axioms audits are exactly
`[propext, Classical.choice, Quot.sound]`; failed audits containing
sorryAx are not accepted evidence. One non-failing simp-style warning
remains. Output is in the command-tool record. No Rust or production
changes, full regression or manifest replay occurred in this step.

## Compiled generic determinant-degree gate

On base `d2e459cd` plus this changeset, `lean/AspisV8R17/MinorDegree.lean`
proves two generic results for any finite square multivariate polynomial
matrix over a commutative ring. If every entry has total degree <=d,
the determinant has total degree <=card(I)*d. The same statement holds
for degree in any specified variable. The proof bounds each Leibniz term
symbolically and never enumerates concrete permutations.

Thus the determinant-degree operation needed for 214*5=1070 and the
separate bounds 214*3=642,214,214 is now kernel checked. The source entry
degree bounds and concrete nonzero-minor certificate still need a compiled
polynomial correspondence; these generic theorems do not discharge them.

Focused command from `/Users/dominic/ZK/AspisFormal`:
`/usr/bin/time -l lake env lean -j1 -M1800 /Users/dominic/ZK/.worktrees/ZK-v8-privacy-repair-20260913/docs/research/v8-full-view-zk-20260912/lean/AspisV8R17/MinorDegree.lean`.
Initial proof failed at simplifying the constant sign coefficient: exit
1, wall 10.28s, peak RSS 1795358720 bytes, swaps 0; the failed audit
reported sorryAx and is not accepted. Replaced that simplification with
the named `totalDegree_C` lemma. Total-degree-only compile then passed:
exit 0, 1.92s, RSS 1795440640 bytes, swaps 0. After adding the per-variable
theorem, final compile passed: exit 0, 2.49s, RSS 1797390336 bytes, swaps
0. Both final `#print axioms` results are exactly
`[propext, Classical.choice, Quot.sound]`. Outputs were captured by the
command tool. No Rust source changed, and the unchanged Rust regression
was not rerun. No full manifest replay or global security claim is made.

Base `291f0623` plus this changeset, 2026-09-21.

The research-only `r17_active_minor_polynomial_witness` constructs the
214-by-699 direct active map using the immutable source transport and
chord multiplication. Columns are ordered by degree 22..254 and then
channel B,C,D. Each column has that channel coefficient one and A equal
to minus alpha, alpha squared, or alpha cubed respectively. It uses
normalized chord `[1+uv,uv-1,-(u+v)]`.

At the single fixed algebraic evaluation alpha=2,u=3,v=4 in M31, rank is
214. The reduction routine independently checks its computed left inverse
times the original selected square matrix equals identity. The exact
214 zero-based column indices are frozen in
`evidence/r17-active-minor-columns.txt`; the test requires equality with
this fixed minor, rather than allowing a different selection silently.

These parameters lie in CM31 and are NOT accepted OOD parameters. That
does not invalidate a polynomial nonvanishing witness: a polynomial with
any nonzero evaluation is not identically zero. No synthetic execution
or claim about the sampler's support is being made here.

## Degree argument and remaining refinement

Regard alpha,u,v as indeterminates over QM31. Quotient entries have alpha
degree at most 3 and no u/v dependence. Chord entries have degree at most
one in each of u,v and total degree at most 2. `times_x` and inverse
transport are fixed linear maps with field-constant coefficients.
Therefore direct matrix entries have separate degree bounds (3,1,1)
and total degree at most 5. Each determinant term is a product of 214
entries. The fixed determinant consequently has separate degree bounds
(642,214,214), and total degree at most 1070. Summation cannot increase
these upper bounds. Its nonzero evaluation above is an executable exact
field certificate, not yet a kernel-checked determinant certificate.

This is an explicit mathematical degree argument based on the inspected
linear routines, not a compiled Rust-to-polynomial correspondence theorem.
The next formal obligation is to represent that polynomial matrix and
certify the fixed minor/degree bridge. Probability accounting additionally
requires a justified source challenge law, including adaptive shared-oracle
conditioning and rejected/repeated draws. No numerical source loss is
claimed yet. H1 point rows, G residual rows, C1 coverage, commitments,
seed expansion, retries/publication and soundness remain separate gates.

## Focused evidence

Only the named Rust test ran, offline/locked/release/jobs=1, package
aspis-prover, --lib, --nocapture, timed with `/usr/bin/time -l`.
Initial compile failed because QM31 has no `from_m31` constructor: exit
101, wall 2.60s, RSS 416645120 bytes, swaps 0. Replaced those three calls
with the existing `ONE.mul_m31` API. The corrected test passed: exit 0,
wall 23.57s, RSS 561201152 bytes, swaps 0. Logs are respectively
`/tmp/aspis-r15-host.drHYn9/r17-active-minor.log` and
`/tmp/aspis-r15-host.drHYn9/r17-active-minor-v2.log`.
No Lean source changed in this step; no new axioms audit is claimed.
After freezing the column artifact, the changed test passed again: exit
0, wall 23.83s, RSS 562708480 bytes, swaps 0; log
`/tmp/aspis-r15-host.drHYn9/r17-active-minor-v3.log`.
