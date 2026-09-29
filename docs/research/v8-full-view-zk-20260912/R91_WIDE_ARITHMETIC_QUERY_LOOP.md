# R91: bounded-width arithmetic and the actual outer query loop

Base `8d84840936fb9338c71b045f527c065b691ba125`; 2026-09-29/30.
Research only. **Neither under-1M execution nor full security is achieved.**

The complete native verifier accepts the same two R84 proofs at
**1,135,747 / 1,134,007 CU**, saving 5,310 / 5,210 against R90.
Both actual 1M honest executions exhaust. The larger fixture is 135,747 CU
over target. Corrupted combined finals reject with Custom(6) at both caps,
not resource failure. Heap remains 262,144 bytes; simulated accounts remain
unchanged. These are verifier-only measurements, not settlement or a universal
all-input resource bound. R84's profile remains unpromoted.

## Native result and failures retained

M31 addition/subtraction use u64 intermediates on the bounded fast path.
The original checked operations remain in cold fallback functions, including
first-add overflow and subtraction-underflow behavior on public raw values.
No global overflow setting or decoder changes. Checks cover 265,536 canonical
pairs against both frozen source and independent u64 arithmetic, and 392 raw
operation cases including matching panics. The retained multiplication,
square, basis, ordinary, opening and gamma gates pass, as do both host proof
audits and 3,282 wire cases (3,281 checked rejections).

The first three arithmetic builds fail the unchanged SBF stack gate:
`build_spend_trace_v4`'s hash closure has a 6,336-byte frame, exceeding 4,096.
Outlining the fallback and trying addition alone do not fix it. These are
failed builds, with no CU result. Inspection finds fixed-array copies of the
22 recorded Poseidon transitions. The private recorder now retains the
already allocated transition Vec, consumes it by ownership, and preserves
the exact round-count assertion. The first rewrite fails because its private
struct still derives Copy; the corrected immutable stage passes all ten
existing trace-v4 tests and the full SBF stack/table gates. No diagnostic is
waived and no larger stack is used. The complete saving above is for the
composed arithmetic/recorder stage, not separately attributed to each edit.

## Proved and compiled boundary

Three focused Lean leaves extend R86's exact extracted inner-loop result:

- `QueryBlockWords`: the runtime chunk iterator produces exactly eight
  four-byte words from the 32-byte block, with no remainder; little-endian
  decoding and the 18-bit mask equal the retained word model.
- `QueryBlockStep`: the actual squeeze performs its ordered squeeze/advance
  hash calls; one actual outer iteration equals the bounded scan, including
  the no-hash exhausted case.
- `QueryLoopExecution`: the actual extracted outer loop terminates with the
  model's output and final transcript state. The model's proved eight-block
  progress bound is used; no artificial fuel result is substituted into Rust.
  The source's extra completion-detection block is preserved.

This is a value/state theorem for a deterministic hash adapter, **not the
public entry guard, complete observed shared-oracle execution, or a random
oracle/privacy/soundness theorem**. The unsupported is-power-of-two/ctpop
templates remain excluded. No new axiom or admission is introduced.

| Final exact target | Exit | Wall s | Peak RSS KiB | Swaps |
|---|---:|---:|---:|---:|
| `AspisV8R19/QueryBlockWords.lean` | 0 | 2.66 | 3,686,060 | 0 |
| `AspisV8R19/QueryBlockStep.lean` | 0 | 3.17 | 3,690,168 | 0 |
| `AspisV8R19/QueryLoopExecution.lean` | 0 | 2.34 | 3,679,548 | 0 |

Lean 4.32.0, base revision above, `lake env lean -j1 -M4500`.
359 compiled predecessors reused, 308 dependency pins, 11 `#print axioms`
audits. Seven use standard Lean axioms; four additionally retain the existing
opaque `core.fmt.Formatter : Type`. No final warnings. Earlier focused
elaboration failures and the warning cleanup remain in the evidence.

## Evidence and next obligations

Run `python3 docs/research/v8-full-view-zk-20260912/tools/check_r91_evidence.py`.
The 189-artifact bundle pins source deltas, failed and successful builds,
fixture/ELF hashes, complete runtime results, exact Lean targets and resource
logs. No keys, fixtures, ELFs or raw register dumps are collected.
The Solana skill's source/malformed/stack/full-runtime gates determine
selection. NUC jobs are release/offline/locked or cached focused Lean, all
with MemorySwapMax=0 and explicit caps: host/Lean 5/7 GiB, SBF 12/16 GiB,
runtime 2/3 GiB, collection 1/2 GiB. Recorded job swaps are zero.

Next sampler source work: close the public argument guard without admitting
ctpop, then connect ordered observations to the existing memoized shared-oracle
law and complete experiment. The first profile security proposition remains
**universal actual-source C1/H1/G joint affine-image compatibility for R84**,
including p0/p2, adaptive/degenerate prefixes and justified exception losses.
Finite certificates are not this theorem. Causal posterior simulation,
seed/commitment composition, visible failure/retry/publication, and coherent
pre-beta quotient-pair extraction remain open. All earlier negatives remain.
No production promotion, deployment, wallet operation or security reduction.
