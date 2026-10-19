# Pre-registration: worst-case CU upper bound for the R1 two-transaction path (2026-10-19)

Written by the lead before any work starts. Criteria may not change after
results are seen.

## Target

The optimised verifier and Pool adapter as merged on `research` (CU-savings
final source 39c2971dd plus later research commits; the job pins the exact
revision and ELF SHA it analyses). Features `pool-adapter,private-leaf-salts`,
no `cu-profiling`. Two transactions: stage 1 and Pool settlement (transfer and
withdrawal).

## Method (fixed)

1. Enumerate every data-dependent cost site: value-dependent branches,
   data-dependent loop trip counts, variable-length syscalls (sha256 and
   others), variable-length parsing, rollover pair count, account-size
   dependence. Sources: Rust source AND the linked SBF ELF's control flow; a
   site found only in the ELF counts.
2. For each site, an analytical maximum extra cost over the cheapest path,
   times its maximum execution count, with the code line that caps the count.
3. Bound B_tx = max measured fixture CU for that transaction + Σ site maxima.
4. Consistency check: with `cu-profiling`, every phase outside the listed
   sites must have identical CU on all fixtures; any unexplained variation is
   a missed site and must be added before a bound is stated.
5. Randomised sweep: ≥ 256 valid accepted transactions per transaction kind
   (random witnesses, masks, tree positions, rollover counts across the
   admitted range), plus targeted inputs driving each site toward its maximum.
   No sweep value may exceed B_tx; one that does voids the bound.

## Acceptance

- PASS: B_stage1 ≤ 1,300,000 and B_settlement ≤ 1,300,000 (each kind), with
  steps 1–5 complete and the sweep maximum ≤ B_tx.
- FAIL: either bound > 1,300,000. Report the dominant sites; no redesign in
  this job.
- INCOMPLETE: any site without a code-cited cap (e.g. an uncapped retry
  loop, or a rollover count with no enforced maximum). Name it; no bound is
  stated.

## Labels

The result is an argument with executable checks, not a formal proof. Rejected
transactions are out of scope (they fail at the sender's cost). Measured,
analytical and swept figures are labelled separately.
