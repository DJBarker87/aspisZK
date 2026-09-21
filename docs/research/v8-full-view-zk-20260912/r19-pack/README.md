# Aspis R19 — channel-fold candidate and exact R18 optimizations

Base: DJBarker87/aspisZK at `77fb78727c8b880b7c029828ad93083ff854f7f6`, branch
`research/v8-r18-sparse-coded-g-20260921`, checked 21 September 2026.

**This is an executable research handoff, not a finished low-CU verifier.**
Independent C++ checks were compiled and run in this environment. Rust and
Lean drafts are uncompiled. No SBF verifier was executed here. The supplied
benchmark figures are explicitly source-reported R18 evidence.

## The two tracks

**Exact R18 track:** establish source redundancy of the 875k-CU internal opening
reference; share query accumulators via rho^22; test canonical arithmetic
specializations; factor the fixed T163 correction. These aim to preserve the
current proof bytes, acceptance checks and transcript.

**New-profile track:** one degree-two channel sumcheck reduces the two different
quotient/functionals to one challenge-dependent quotient/functional BEFORE the
existing PCS path. This can remove one Final256 and the separate first-MLE
terminal computation without claiming the invalid old single-functional identity.
It adds two visible fields and one challenge, so source extraction, new-message
privacy and the real shared-oracle law are mandatory new obligations.

The proposed fixed field region changes from 953 to 699 values: 4,064 fewer
bytes in that region. No total proof-size or CU saving is claimed as measured.
The channel fold alone has not been shown sufficient for 1.4M CU.

## Start here

Read `CODEX_TASK.md`, `design/CHANNEL_FOLD.md`, `design/UNCHANGED_PROFILE.md`
and `design/BUDGET_AND_DECISIONS.md`. Source pins and reported costs are in
`SOURCE_PINS.json` and `evidence/source_reported_cu.json`.

Run the independent checks:

```sh
python run_checks.py
python tools/generate_correction_plan.py
```

The second command reproduces the exact signed fixed-map tables. Before using
them in a real staged verifier:

```sh
python tools/check_stage_inventory.py /path/to/stage/r17_basis_tables.rs
```

This script deliberately refuses an unknown/nonliteral inventory. The packet
contains no network operation, deployment, remote write or wallet operation.

## What passed here

- 192 full-QM31 fixed-map factorization cases; 24 also use an independent
  full chord/adjoint construction.
- 96 shared-query cases and 384 intermediate stage checks.
- 1,024 quotient/fold linearity cases.
- 200,049 canonical-arithmetic cases, reduced-width exhaustive multiplication
  checks, and negative controls including misuse of the one-fold reducer.
- 48 complete source-shaped channel-weight tests, with arbitrary image residuals,
  plus 192 folded-weight tests.
- All 28,830 F31 quadratic error polynomials with a false boundary, verifying
  at most two roots each. This does NOT establish a source Fiat–Shamir law.
- Exact signed-operator table reconstruction over the integers.

See `evidence/VERIFICATION.md`. Model tests do not certify actual Rust behavior,
source privacy/soundness, real q22 sampling, or a supported-budget execution.

## Files

`src/` holds Rust integration drafts and generated tables. `tests/` holds two
compiled independent checkers and their retained R18 algebra model. `lean/`
holds six uncompiled scalar algebra leaves. `tools/` supplies reproducibility
and source-inventory gates. The mathematical design and precise next source
obligations are in `design/`, rather than being hidden in a launch prompt.
