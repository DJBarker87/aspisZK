# Codex execution packet: delete the dense verifier work

Start on `research/v8-privacy-repair-20260913`. Reviewed HEAD is
`6677d5f1310ff7373301fbd79f186278f772e68a`. Inspect the current head first;
preserve intervening work and the R43 preferred endpoint. Work locally in a
new research worktree/profile; do not deploy, merge, force-push or use wallets.
Do not run long unchanged formal suites before the first actual source/SBF
screening. The goal is a working low-CU verifier, not more equivalent dense
implementations. All source gates below still apply.

## 0. Preserve correct baselines and evidence

R43 is 16,456,519 primary CU on the retained v2 proof. R44 is 18,281,174,
not a faster result. Both complete diagnostics heap-fail in their second
reference pass. Reuse source-pinned staging and cached toolchains.

The supplied C++ is source-shaped arithmetic, NOT extracted Rust. It uses
synthetic rationally parametrized raw points, NOT the real q22 sampling law.
Its G rank 601 and H1 rank 540 are screening evidence, not authorization to
publish. Read the negative controls before changing any source.

## 1. First profile: sparse G, unchanged current T

Use a fresh explicit profile ID from initialization, for example:

    AV8/R18/sparse-coded-G128-step3/two-channel/research-v1

Keep source query count 22, two channels, all 953 field observations, both
Final256 arrays, all ten semantic rounds, all four relation rounds, all image
residuals, component OOD and packed authentication. Keep current T and pivot.
No challenge gets replaced by a small constant.

A. Replace the G coin extractor with `g[order[128+3*i]]`, i=0..270. It must
   consume the same balanced G supplied by the real source mask builder.
   Do not resample these coins or replace the seed expansion law by IID.
B. Keep the structured mask_eval and round polynomial formulas in u exactly.
   The initial G contribution becomes u[0], as in the existing structured
   construction. Update producer, verifier, audit and reference routes
   consistently. Eta remains sampled AFTER the initial claim.
C. Use the supplied split/join codec (or a source-equivalent implementation)
   to retain the 752 remaining legal G coordinates. Test both inverses.
D. Prover/host-reference may scatter the original-row weight to order[S].
   Verifier code-space sparse weights are directly at S. Do NOT apply the
   old permutation/pivot correction a second time to the sparse component.
E. All S>2, so the sparse component contributes zero to the code coefficient
   0/1/2 interpolant subtraction. Include the ordinary E1/E2 and inactive
   parts, which are not zero. Both use_x branches must be checked.
F. In the terminal, use the existing pinned grouped geometry and the supplied
   sparse contraction. Keep 64 high groups, the group-64 zero extension,
   513/514 chord arithmetic boundaries and the source four-fold convention.
   Add the existing image and fresh-query terms separately.

Use caller-owned buffers. `[K;271]` is 4336 bytes, already over one SBF frame:
DO NOT return it by value in the SBF caller just because the host draft does.
The `mixed_coins` draft is for prover/reference; add an `_into` version for
any SBF path. Place 271 coefficients plus 128 group-sum fields in bounded
reused heap storage and check actual emitted frames. No new per-node Vecs.

## 2. Mandatory source screening BEFORE a new privacy claim

Extend the actual test-only r16_final_posterior.rs placement dispatch with
this distinct CODE-space placement; do not overwrite old First271/Vandermonde
controls. On at least both genuine accepted source prefixes:

- Rebuild the full 624/625-row G map using the complete selected terminal,
  original 87 point fields, sequential OOD, both finals and first relation.
- Verify all original equations and the precise compatibility identities.
- Construct the actual opposite-witness correction after C1/H1 have changed.
  Check the affine offset target, not just homogeneous rank.
- Check both image inclusions if the source matrix differs between contexts.
- Reevaluate every retained semantic coefficient and point/quotient/opening
  value using the real producer, not the screening model as its own oracle.
- Keep the same legal mask constraints and failures; verify actual source
  mask-application acceptance and source-generated raw queries.
- Keep the original C1 q4/q6 separator against the unrepaired source. The
  repaired profile's raw first-89 coefficient argument must not be regressed.

Preserve the current same-public witnesses. Reject a candidate on an observed
new obstruction; do not relax an equation to restore rank. The new map still
needs universal compatible-image coverage and exceptional-prefix accounting.
An isolated full-rank example is not that proof.

## 3. Share common functionals; do not collapse the proof channels

Let A be the transported/chord/fold ordinary functional and E the same map
on ordinary first-point weights. H is the new sparse G functional. Compute

    dot(FinalR+FinalG, A) - kappa*dot(FinalG,E)
        + kappa*dot(FinalG,H)

for the BASE terminal. Retain separate channel image/query contributions.
This is an arbitrary-vector linear identity. It is NOT permission to remove
the G channel, its OOD claim, Final256, image constraint or raw openings.

Reuse the ordinary tensor/correction geometry across A and E; combine weights
or right-hand contraction coefficients BEFORE evaluating repeated common
blocks. Do not independently expand two ordinary vectors. Reuse prepared
field multipliers and existing sum_products kernels only under their bounds.

Fresh q22 query covectors begin after alpha0. They must not pass through the
original T/chord transform or the first dual fold. Preserve the disjoint
rho powers 1..22 and 23..44 and all boundary/terminal equations.

## 4. SBF performance gate now, not after another proof campaign

Produce new-profile honest fixtures and verify through both complete host
implementations. Mutations, wrong profile, truncation, noncanonical limbs,
invalid witness, malformed finals and poles must be rejected appropriately.

Compile the primary SBF verifier with the actual frame gate and unchanged
heap budget. Instrument at least: semantic, ordinary description/terminal,
sparse-G coefficients/contraction, openings/authentication, fresh queries,
final folds and total primary acceptance. Record all instructions/checks.

Benchmark primary-only production-shaped and double-verification diagnostic
binaries separately. They must have distinct names and recorded source flags.
A 100M diagnostic endpoint is NOT a supported transaction. Measure normal
1.2M and 1.4M budgets, successful valid proofs and completed invalid rejections.
A failure total is never reported as a successful verifier CU count.

Do not count eliminating the second reference pass as a saving against the
already primary-only 16.46M checkpoint. Do not increase compute or heap caps
to declare success. Keep the dense reference permanently in host/CI tests.

The gate for this experiment is: actual source correction still works and
the G FFT/tree/dense expansion is absent from the SBF path. Then measure the
remaining gap. Do not preannounce a guessed CU total.

## 5. Second independent profile: minimum-support T

Only after the first sparse-G profile has been screened and measured, test
src/minimal_support_transport.rs under a SECOND fresh profile ID.

Feed it the current source constructor's exact first 89 pad rows. Keep those
first 89 images and pivot1023, but complete the permutation by fixing every
index outside their union with 0..89. The checked inventory gives support163
rather than479. Verify source legality at all 16 C1 columns, permutation
uniqueness, both inverses, both dual pairings and all 89 balanced unit images.

Freeze compact support positions/cycles as constants from the actual source.
Evaluate only those 163 original coefficients, and contract only those
weighted differences. A 479-element vector is not justified by maximum index
478. Keep fixed inactive/pivot contributions. Apply T to all columns that
share the PCS batch and inverse-dual to every original functional.

The modeled H1/G ranks remain540/601, but run the complete source H1 active,
point/OOD/raw/final offset corrections and source C1 differences again.
Reprove/rebind the active-minor and compatible-image certificate as needed;
old selected columns and source indices cannot be inherited by name.

DO NOT use the superficially cheaper bit-affine pivot13 map in this pack.
It drops H1 rank to517 despite passing G/raw and inverse tests. That failed
branch is a negative control, not an alternative that can be auto-promoted.

## 6. Remove experimental duplication without weakening the verifier

Audit the internal opened_values_reference call as well as the second full
verifier. Identify exactly which checks are duplicated and which are unique.
The packed canonical decoder, domain/pole checks, paired Merkle root check,
quotient/image equations, 44 consistency equations and relation acceptance
must each remain in the primary. Prove arbitrary-canonical-input equivalence
for any reference-only assertion moved to host/CI. Preserve all error cases.
Keep corruption and differential tests; do not retain expensive independent
recomputation inside the eventual production entry point by accident.

This removes testing duplication, NOT protocol checks. Where redundancy is
not proved, report that precise obligation rather than deleting the check.

## 7. Formal/security closure and deliverables

After source and performance gates, compile the smallest new leaves:
- slot injection and full 271+752 codec;
- T^-transpose cancellation for sparse coefficient-space weights;
- sparse grouped contraction incl. carry and high-tail support;
- common-channel pairing for arbitrary inputs;
- optional minimum-support permutation and its exact first89 correspondence.

Then universal source compatible-image coverage, adaptive loss accounting,
shared seed/oracle chronology and a public-only complete simulator. Preserve
existing soundness extraction/image/Fiat–Shamir gates for the changed profile.
Neither sparse mixing nor a basis permutation inherits end-to-end security
merely because it is invertible. Do not add a hiding/rank/uniformity axiom.

Return changed files; exact profile and commit; compile/test/axiom evidence;
actual primary and whole-program SBF results; remaining CU by stage; and the
first unresolved mathematical/source statement. Include rejected attempts.
No arbitrary bit-security or throughput claim. Optimize toward a complete
supported-budget verifier plus settlement headroom, not a standalone kernel.
