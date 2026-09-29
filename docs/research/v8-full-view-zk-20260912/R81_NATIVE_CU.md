# R81: native execution wins, unchanged repaired protocol

2026-09-29. Control: `4b64f97254e18f0338e1ad6229ca8407143aeb2b`,
R69 runtime. User priority is now the complete under-1M CU gate, without
weakening security. R80 observer/formal work is paused. No new Lean work ran.

## Complete measured executions

Same two frozen R19 proofs, clean primary verifier, same driver and 262,144-byte
heap. Neither a partial checkpoint nor a microbenchmark is used as the total.

| Candidate | World 0 CU | World 1 CU |
|---|---:|---:|
| R69 control | 1,495,663 | 1,497,050 |
| Guarded square | 1,468,197 | 1,469,590 |
| Also delayed-reduction short dots | 1,439,254 | 1,440,522 |
| Also defer unused semantic polynomial | 1,425,186 | 1,426,443 |
| Binary powers and rotation scaling, outlined short dots | 1,417,341 | 1,418,557 |
| Inline short dots, without new powers/scaling | 1,406,069 | 1,407,329 |
| Compose those wins | 1,398,224 | 1,399,443 |
| Also private canonical basis arithmetic | 1,385,494 | 1,386,734 |
| **Also reuse ordinary adjoint for scalar G** | **1,356,211** | **1,357,487** |

The selected R81 endpoint saves **139,452 / 139,563 CU** against R69.
It still needs **357,487 CU** off the more expensive fixture. Both honest
proofs **exhaust at the actual 1,000,000-CU cap**. Diagnostic-cap acceptance
is not budget success, production readiness, or settlement-transaction cost.

Every listed candidate compiled without SBF stack-frame overflow diagnostics,
accepted both complete honest proofs at the diagnostic cap, and passed all
3,281 host wire controls (3,280 checked rejections, one positive). Corrupted
finals receive `Custom(6)` at the diagnostic cap. Some now also reject before
1M; resource exhaustion and checked rejection are recorded separately.

## Exact arithmetic changes

- Squaring uses the retained guarded R69 multiplication on equal operands.
  The old square remains the literal fallback for noncanonical raw values.
- Arity 2/3/4 products reuse the retained guarded raw product, accumulate its
  four partially reduced residues, then canonicalize once. At most four
  terms and a canonical constant fit below 2^37. Original arity, prepared-
  value and noncanonical fallbacks remain. Inlining this small kernel wins;
  this is not a global arithmetic-safety switch.
- The cached semantic path no longer constructs a polynomial it does not
  consume. The empty-cache path still constructs it; host builds retain an
  independent old-evaluation assertion with the correct incoming claim.
  Transcript absorption, challenges and coefficient order are unchanged.
- Semantic powers share squares; inverse powers of two use canonical
  31-bit rotations with the original scalar-multiplication fallback.
  The private `Q` basis kernel validates on entry and preserves its invariant
  internally. Its limbs are private; the unchecked constructor is removed.
  Its multiplication is the retained bounded R69 formula, not a new field.
- Ordinary `terminal_scalar` already computes the high/final adjoint and
  leaves it unchanged at workspace coordinates 403..531. G immediately
  reuses that verifier-derived result. The exact selected code rows remain
  `128 + 3*i`, for all 271 coins. Grouping by low coordinate gives 16 normal
  and three carry contractions, followed by the retained scalar low kernel.
  The row-64 zero extension, eight halvings, beta/kappa scale, pivot and
  separate image contribution remain. No cache is provided by the prover.

The old four-output G implementation remains in source and is compared in
host verification. The no-cache fallback still computes its old contribution.
The source postcondition and sparse scalar are checked independently against
the retained coordinate kernel, not only against an honest fixture.

## Focused executed checks

The selected endpoint records:

- 265,536 square cases, including 65,536 boundary combinations and an
  independent u128 formula; 60 raw-constructor square fallback cases.
- 49,152 short-dot comparisons plus raw dot and affine-constant fallback
  controls; retained R69 multiplication checks also run.
- 8,192 basis vectors, 90,112 power-of-two scaling comparisons, 2,560 semantic
  rounds, 12 raw basis and 132 raw scaling cases.
- 796,608 private-kernel multiplication/add/sub comparisons; canonical
  outputs and rejection of noncanonical constructors are checked.
- 256 arbitrary scalar-G cases, every one of the 271 selected basis inputs,
  and 256 checks of the ordinary workspace postcondition. The existing
  tensor, poison-unused-workspace, gather and two genuine public-input
  comparisons remain.

These are source/differential execution checks, not universal Rust refinement
or a new full privacy/soundness proof. No masking, T163, sparse-G map, proof
format, shared-oracle schedule, canonical decoding, domain check, Merkle
authentication, image condition, final relation or old negative regression
is removed or weakened. Existing global security obligations remain open.

## Evidence and next work

`tools/check_r81_evidence.py` audits 222 artifacts, all variant source deltas,
207/209/210 source pins, frozen references, proof/driver/ELF hashes, complete
runtime results, per-command time/RSS/swap and available cgroup receipts.
Repeated source/log files are content-addressed under `evidence/r81-native`.
No private fixtures, keys, ELF binaries or raw register traces are committed.

The exact-text R69 and R81 traces identify actual executed costs. The newer
private-basis world-0 trace exactly matches 1,385,494 CU. It still has 247,110
exclusive instructions in generic multiplication, 113,730 in checked dots,
110,106 in the opening caller and 105,398 in packed combination. These are
exclusive instruction counts, not independent inclusive CU estimates.

All heavy work used cached release/offline builds on the Tailscale NUC,
overflow checks enabled, explicit memory limits and zero swap. Maximum
simultaneous reservation was 26 GiB. Early jobs used capped scopes but did not
persist cgroup properties; that missing evidence is stated, not fabricated.
The Solana skill's source-tests → stack-safe SBF → complete simulated execution
gate was retained. No deployment, wallet operation or production path changed.

Next: native ordinary two-product contraction against the new short-dot
kernel, then measured arithmetic-call layout and packed affine contraction.
Only complete-execution winners will be composed. Full privacy/soundness work
does not resume ahead of the user's CU priority.
