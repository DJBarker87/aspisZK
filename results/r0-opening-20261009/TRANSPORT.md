# R-G — D13's fixed transport

Implemented from base `e5d4e1a3d6fc87e9d99046165fe5c9f81335ba91`.
Executable source commit: `c005349eb063dec231bbc2c14ac58069661e8ecc`.

`aspis_core::r0::transport` implements the permutation from
[the historical order rule, lines 10–63](../../docs/research/v8-full-view-zk-20260912/tools/r16_basis_transport.rs),
as reinstated by [PLAN Decision D13](../../docs/research/v8-r0-rust-20261009/PLAN.md).
It uses only the permutation, not the old `forward` function's pivot-sum
replacement or its subtractive dual.

The [inventory generator](../../crates/aspis-statement/examples/r0_transport_inventory.rs)
derives the first 89 pads from
`pool_v1_pair_forest_relation_free_mask_cells_v1` and
`pool_v1_pair_forest_copy_active_rows_v1`, excluding historical row 1014.
It asserts exactly 89 pads and the legality/inactivity of pivot 1023.
The core includes the generated pads and constructs both 1024-entry tables
at compile time. The remaining rows are increasing, with pivot 1023 last.
This keeps the existing statement→core dependency direction and adds no
runtime dependency, allocation, or prover-selected permutation.

[transport-kat.json](transport-kat.json) contains all 1024 entries of π,
all 1024 inverse entries, the pads, and the table hash. Hash encoding is
**π[row], 1024 unsigned 16-bit little-endian entries**, exactly 2048 bytes:

```
f80af2abf26648dd490b8cdf78914db08ef94b31009103d5cf98ea0a7b802213
```

## Diff and index contracts

- `transport.rs` / `transport_pads.rs`: `ROW_TO_COEFFICIENT` is π;
  `COEFFICIENT_TO_ROW` is π⁻¹; `to_coefficients(t)` is t∘π⁻¹;
  `to_rows` is its inverse. Pivot values remain unchanged.
- `Commitment::new` still accepts row-indexed messages, retains those rows
  for its commitment-match check, and encodes their transported coefficients.
  Both C1 and C2 therefore commit `W_l = Enc(t_l ∘ π⁻¹)`.
- `prover::prove` still accepts row-indexed messages. Endpoint evaluations
  and every honest quotient solve use their transported coefficients.
  The generic `quotient` and `EncodingDomain::encode` APIs accept natural
  coefficients; callers must not transport their outputs again.
- `opening::eq_weight` and `indicator` are coefficient-indexed. Verifier
  `claim_prime`, quotient weights, total weights and V2 inherit that fixed
  indexing through `OpeningData`. Interpolants and e1/e2 already operate on
  natural coefficients and receive no extra permutation.
- `v_honest` pairs transported messages with the transported inactive
  indicator. Tests independently compare it with the original row sum.
- `honest_claims` uses the unchanged row-space multilinear formula, now
  named `row_eq_weight`. The 87 semantic claims and three row points keep
  their original meaning.
- The Python opening oracle independently reconstructs π from the inventory
  pads and updates the weight digest, claimPrime, reconstructed c4, and later
  transcript states. The wire format and proof length are unchanged.

## Validation

All checks used optimized release arithmetic with overflow checks and two
compiler jobs on `nuc`, reusing the R-F compiled cache. Each invocation ran
in a separate systemd scope with MemoryHigh=4 GiB, MemoryMax=6 GiB and
MemorySwapMax=0. The reservation snapshots show no other active user build
scope at the five final gate starts; host available memory was about 51 GiB.
Expected heavy work was compilation, then full-domain natural-basis encoding
and Merkle hashing. The quotient elimination remains sparse/banded.

| Gate | Exit | Wall seconds | Peak aggregate RSS MiB | Cgroup peak MiB | Peak swap bytes |
| --- | ---: | ---: | ---: | ---: | ---: |
| [Core R0 tests](rg-core.json), 11 passed, full-size deferred | 0 | 32.857 | 810.621 | 762.586 | 0 |
| [Inventory generator --check](rg-inventory-check.json) | 0 | 28.246 | 1047.934 | 820.594 | 0 |
| [Statement inventory test](rg-inventory-test.json) | 0 | 0.402 | 185.273 | 93.844 | 0 |
| [Independent opening KAT --check](rg-kat-check.json) | 0 | 0.201 | 31.512 | 16.703 | 0 |
| [Full-size round-trip and teeth](rg-full-size.json) | 0 | 4.118 | 294.613 | 283.797 | 0 |
| [no_std library check](rg-no-std.json) | 0 | 2.311 | 544.867 | 464.828 | 0 |

The core tests cover bijection, inverse, unchanged pivot, both 1024-entry KAT
tables, pairing invariance, every Boolean row's transported eq weight,
every inactive indicator entry, preservation of all 87 arbitrary-E row
claims, and the v/weight identity. The statement test derives the pads again
from the live inventories and checks inactivity and eligibility separately
for all sixteen columns, including the pivot. Existing chord, quotient,
fold, parser and sampler/schedule tests also pass.

The full-size gate commits all 29 × 2²⁰ values and verifies an honest
83,742-byte opening proof. It checks the quotient identity at every domain
point for a full-support K lane and the coefficient identities for all
29 quotients. All existing corruption teeth pass: six wire corruptions,
reauthenticated F/Y rejection by V1, v and all six transmitted polynomial
coefficients rejected by V2, and independent V1/V2 predicate tests.
Internal timings: commitments 1.449979 s, opening prover 0.890461 s,
opening verifier 0.025860 s. These are host timings, not CU measurements.

The transported synthetic fixture is [transport/honest-proof.bin](transport/honest-proof.bin),
with roots, states, queries and proof hash in [transport/fixture.json](transport/fixture.json).
The earlier R-D proof and logs remain historical evidence at their recorded
source revision. This fixture still uses an accepted synthetic semantic
boundary; it is not an end-to-end payment proof.

[rg-source-manifest.json](rg-source-manifest.json) pins 159 source/oracle
inputs; [rg-source-audit.json](rg-source-audit.json) verifies all of them
against the Linux workspace. The core suite ran immediately before the
source commit under the label `e5d4e1a3d+rg-working`; its executable inputs
are unchanged in `c005349eb`. No unchanged full regression was repeated.
Exact commands are recorded in each gate JSON; logs have the same stem.
[run_transport_checks.py](run_transport_checks.py) reproduces the five final
gates with the caps and source audit, using `CARGO_TARGET_DIR` for the cache.

The first runner invocation failed before Cargo started because a non-login
SSH PATH lacked Cargo. [rg-runner-path-failure.log](rg-runner-path-failure.log)
is retained. The runner now adds the user's Cargo bin directory to PATH.
There was no proof, compilation or memory-pressure failure in that attempt.

`#print axioms`: not applicable. This is Rust implementation/test evidence;
no Lean source, theorem premises, formal release gate, SBF build, or CU
measurement was changed or claimed.

## Handoff to Rust A / R-E

Pass **row-indexed** lane messages to R-D's `Commitment::new` and `prove`.
Use the semantic boundary immediately before z0; opening `prove` generates
the transported beforeZ1 endpoint record itself. R-F's existing diagnostic
row-26 endpoint builder still evaluates raw row arrays; R-E must use R-D's
transported y0 when assembling its one P1 proof, or transport that diagnostic
evaluation before reusing it. Its semantic row claims remain unchanged.
R-G intentionally does not implement the end-to-end handoff, fixtures, probe,
or CU work assigned separately to Rust A.
