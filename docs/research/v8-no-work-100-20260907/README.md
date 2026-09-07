# V8 no-work 100-bit research — bounded screen and prototypes

Start with [report.md](report.md). See [security-contract.md](security-contract.md),
[baseline.md](baseline.md), [ledgers-and-candidates.md](ledgers-and-candidates.md)
and [sources.md](sources.md) for the contract, pins, applicability and primary sources.
[candidates.json](candidates.json) retains exact rationals and flags;
[candidates.csv](candidates.csv) is the compact index. Unmeasured is never zero cost.

Branch: research/v8-no-work-100-20260907. Worktree:
`/Users/dominic/ZK/.worktrees/ZK-v8-no-work-100-20260907`.
Base: `4c91f97ac6576201f90d41c2a575e54c026e3796`. Date: 2026-09-07.
No deployment, push, remote build, production mutation, witness upload, paid
infrastructure or subagents. Concurrent main/V8 work was preserved.

Host: Apple M3 / Mac15,13, Darwin 25.5.0 arm64, 25,769,803,776 RAM bytes.
Rust/cargo 1.93.0. gh, Python3, jq, curl, pdftotext, cargo-build-sbf and elan
Lean/lake launchers are installed. These are not a cached Linux release build
environment. The repository's SBF workflow requires Linux x86_64, finite cgroup
limits and zero swap. No large build was launched. Standalone optimized Rust
avoided dependency rebuilds; executed jobs stayed far below 8 GiB.

## Reproduce from the worktree root

```sh
python3 docs/research/v8-no-work-100-20260907/experiments/feasibility.py --test
python3 docs/research/v8-no-work-100-20260907/experiments/independent_fields.py
rustc --edition=2021 -O docs/research/v8-no-work-100-20260907/experiments/fields.rs -o /tmp/aspis-v8-fields
/usr/bin/time -l /tmp/aspis-v8-fields
rustc --edition=2021 -O docs/research/v8-no-work-100-20260907/experiments/schedules.rs -o /tmp/aspis-v8-schedules
/usr/bin/time -l /tmp/aspis-v8-schedules
rustc --edition=2021 --test -O -A dead_code docs/research/v8-no-work-100-20260907/experiments/production_field_tests.rs -o /tmp/aspis-v8-production-field-tests
/usr/bin/time -l /tmp/aspis-v8-production-field-tests
```

The schedule benchmark links macOS System/CommonCrypto; port its callback before
Linux use. Seeds are public/synthetic. It is not the complete verifier. Field
sampling timings exclude SHA/RNG generation and do not benchmark secure entropy.

From this research directory, verify the deterministic artifact:

```sh
set -o pipefail
python3 experiments/feasibility.py | diff - candidates.json
```

The exact DP counts q-subsets by frontier with left/right subtree convolution.
Independent checks exhaust depths 1–4, q up to five; verify binomial totals and
falling-product query arithmetic. Production probabilities use exact integers/
rationals; floating logs are display only. Exhaustion records preserve exact
base and power instead of thousands of decimal digits.

Field certificates use Rabin's criterion for X^5-X-6 and Euler's nonsquare test
for u in the pinned QM31 tower. Independent Python uses polynomial arithmetic
modulo p and the alternate quartic u^4-4u^2+5. Both certificates passed, as did
1000 extension arithmetic cases and all 32 production field tests. These are
executable certificates, not Lean formal proofs.

Logs under experiments/ retain timings/RSS/swaps. Final field prototype:
0.46 s / 1,671,168 B RSS; search 0.83 s / 2,015,232 B; production field tests
0.37 s / 3,063,808 B. All exit 0, zero swaps. Counters apply to execution, not
compilation or proving. Prior V8 Lean/rank/prover and V7 CU evidence is reused.

Development corrections: first standalone invocations had an incorrect relative
include, omitted edition=2021, and direct production-field testing lacked
`extern crate alloc`. Research wrappers corrected these without production edits.
Python initially hit its integer-string digit guard on the 64th-power output;
the exact base/power representation fixed serialization. An initial cap245
search was replaced with the correctly matched cap246 experiment. No heavy
job was retried with a larger memory cap.

## Status and bounded next work

- Gate 1: source/census/combinatorics completed; full theorem applicability and
  NI/privacy claims remain unresolved for every serious candidate.
- Gate 2: small fields, samplers, hints and hiding-falsifier prototypes executed;
  prior two-OOD rank evidence reused. No new dense elimination.
- Gate 3: not entered; cryptographic predecessors have not passed, and a matched
  Linux SBF environment is unavailable locally.
- Gate 4: not entered; no Lean changes or formal release/axiom replay claimed.

Next: the exact chord quotient-to-circle-encoder/fold experiment in report.md,
then restored tuple-family/source and privacy proofs if it survives. Only then
obtain authorized capped Linux four-shape complete-transaction measurements.
