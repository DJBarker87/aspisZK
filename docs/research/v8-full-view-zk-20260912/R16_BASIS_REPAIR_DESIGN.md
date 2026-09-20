# R16 candidate: public basis transport for existing C1 masks

This is a repair candidate, not an implemented protocol or privacy claim.
It addresses the raw C1 defect directly; the previous negative regression is
retained. No new randomness distribution or hiding assumption is introduced.

## Candidate map

Let I be the actual inactive row set and p=1023 the existing balancing row.
Choose 89 distinct rows in I excluding p and the positive-transfer special
row 1014, each certified by the source mask-cell inventory as relation-free
in all 16 witness columns. Let π list these first, all other non-pivot rows
next, and p last. Define a common public linear transform T on 1024 rows:

- `(Tm)[j]=m[π(j)]` for j<1023;
- `(Tm)[1023]=sum_{r in I} m[r]`.

The inverse copies the non-pivot coordinates back and sets
`m[p]=(Tm)[1023]-sum_{r in I, r≠p} m[r]`.
For each selected pad row r=π(j), `T(e_r-e_p)=e_j`. Thus balanced, legal
existing mask directions become the first 89 independent code coefficients.
No active witness cell is resampled, and no relation constraint is waived.

For any original linear weight w, set transformed weights
`w'[j]=w[π(j)]-w[p]` on non-pivot inactive rows, `w'[j]=w[π(j)]` on active
rows, and `w'[1023]=w[p]`. Then `dot(w,m)=dot(w',Tm)`.
This gives the required direction of verifier weight transport; applying T
to both vectors is not correct in general.

## Required protocol integration, not performed yet

The current encoder treats message rows directly as code coefficients,
without an AIR interpolation. Candidate encoding is `E(Tm)` instead of
`E(m)`. T must be common to every column entering the same linear PCS batch;
changing only C1 while keeping an incompatible C2 batch is not justified.

Keep semantic construction on the original message rows. Transport the
linear point/claim weights through the inverse transpose, and make OOD
evaluation, quotient construction, decoding and verification refer to the
same transformed encoded polynomial. Check every image/terminal constraint
and optimized path. A change to encoding requires a distinct source/profile
binding: old pinned artifacts must not be relabeled as repaired ones.

The transport is invertible and preserves code dimension, but those facts
alone do not establish soundness of the integrated protocol.

## Verification sequence

1. Test inverse/dual identities on all 1024 basis vectors and map all 89
   selected legal balanced directions to the intended coordinate vectors.
2. Test that the actual encoder's first 89 basis directions cover all 88
   raw observations of the retained bad q22 schedule, using an identity
   target rather than just the chosen witness difference.
3. Prove universal raw coverage for distinct source query points. The
   correspondence between this coefficient block and a full circle
   polynomial space must be proved; do not infer it from one matrix rank.
4. Implement and test complete source/dual transport and correctness, with
   the original negative regression still testing the original encoder.
5. Prove joint conditional coverage after the earlier transcript and through
   remaining observations. The 89 directions are reused, not refreshed after
   an observation. Reconcile the R11–R14 posterior with the changed PCS map.
6. Close source randomness/oracle, retry/publication, full simulator and
   soundness obligations before any repaired-profile release claim.

The test-only prototype is `crates/aspis-prover/src/r16_basis_repair.rs`.
Its deterministic row selection and legality assertions are part of the
candidate specification. Production encoding and verification are unchanged.

## First focused evidence — 2026-09-20

Base revision `f0966d2d`. Both candidate tests passed:

- all 1024 basis vectors round-trip and preserve dot products against one
  deterministic dense weight vector; all 89 selected balanced pads map to
  the expected coefficient vectors;
- the retained q22 schedule `[4,6] ++ [1000+7919*i | i=0..19]` has rank 88
  against the first 89 actual circle-encoder coefficients. The existing
  certifier returned and verified a correction for the entire identity
  target. This is one schedule, not universal or joint-view coverage.

Command: `cargo test --offline --locked --release --jobs 1 -p aspis-prover
--lib r16_basis_repair -- --nocapture`. Exit 0; 16.64 seconds wall;
498941952-byte peak RSS; zero swaps; tests 0.05 seconds, two passed.
Time was in compilation, not the small 88-by-89 elimination.
No Lean theorem changed or compiled; axioms audit is not applicable.

The first integration-test placement failed at compile time because the
encoder's basis evaluator is crate-private (exit 101, 24.79 seconds,
467566592-byte peak RSS, zero swaps). The prototype was moved into a
`cfg(test)` unit module; the production API was not widened. No test premise
was weakened and the original C1 failure remains untouched.

The paused SHA nonce experiment remains separate and uncommitted; its
already-running host build completed successfully (123.44 seconds,
683393024-byte peak RSS, zero swaps). No nonce search or host proof was run
as part of this repair milestone.
