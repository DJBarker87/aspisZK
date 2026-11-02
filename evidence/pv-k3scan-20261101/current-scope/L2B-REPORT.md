# L2B source-trace handoff

Target not yet established. Branch `codex/pv-l2b-20261027`, candidate `c57a344726745387efb38d1571d885c69ce829ee`. No shipped-code changes; no push.

## Proved and retained

Lean checks the capped rejection scan and its supplied-UInt32 scalar control projection, rejection/value relabeling invariance, cursor/refill arithmetic, exact ideal IID scalar and entropy-pair mass factorizations, entropy short-circuit classes, conditional guard algebra, and joint observation transports. These are mathematical/model and local source-helper results. They do not instantiate the complete deployed RunJoin observer or prove concrete SHA is IID.

Per-site statements and missing native/caller invariants: [SITES.md](SITES.md). Endpoint before/after accounting: [PREMISES.md](PREMISES.md). V352, V354, V357 and V360 remain OPEN / P; no endpoint premise was removed, added, weakened or moved into T. The trust record remains exactly entropy_law, entropy_kernel, observation.

N2: zero active padding and balanced inactive sum. N3: canonical base/extension limbs and actual parser round-trip. N4: whole noised-column rebalance, same public inactive-row set and canonical native folds. N5: helper producer/consumer multiset identity, pole-free inverse boundary and padding preservation. N6: actual oracle/degree-27 interpolation/running-claim identities. Native associations remain as specified in SITES.md. No checked honest-valid counterexample was found. N1 and N7 were not worked.

## Simulator samplers

* Scalar: q=2^-31; capped geometric rejection count r<16 has mass q^r(1-q), exhaustion q^16=2^-496. Each accepted value has mass q^r/(P+1), so successful output is uniform on [0,P) independently of the retained count. Run four scalar samplers left-to-right for QM31, retaining the first failed prefix. Cursor reads use offset 4(n mod 8); project the logical block ordinal to the u64 counter. E2/freshness/read-bound/native association remains.
* Entropy: test the public nonce first. For nonzero nonce and successful IID 64-byte fills, z=2^-256, q=2z-z², cap 16. Rejected classes have masses z and (1-z)z, conditional weights z/q and (1-z)z/q; they execute one and two predicates respectively. Independently sample the successful pair uniformly among nonzero 32-byte pairs. E1 must also supply the actual OS/error/partial-fill schedule; option-B failure independence remains P.

All are source-trace statements. Physical timing transfer still retains substantive V371 under DOITM OFF, as detailed in [V371.md](V371.md).

## Receipts and stop

100/100 Lean attempts: 96 successful, failures 53000 (fixed shared-root launcher rejected external source), 53043 (large-numeral normalization), 53046 (extra tactic after symbolic rewrite closed the goal), 53100 (sum-binder parsing). Replacements changed the execution root or proof source; failures remain retained. 6/6 optimized, no-stub control-only Kani runs passed; they are not whole shipped-function equivalence gates.

Audits 53297–53299 all exit 0. Every new theorem has an axiom report; successful outputs use only a subset of propext, Classical.choice, Quot.sound. Peak Lean process RSS: 1,905,504 KiB; swap 0. All scopes use MemoryHigh=6G, MemoryMax=8G, MemorySwapMax=0, TasksMax=64 and Lean -M7000. No cap was raised.

| Final focused target | Attempt | Exit | Wall | Peak RSS KiB | Swap | Revision |
|---|---:|---:|---|---:|---:|---|
| PV_L2B_Rejection | 53019 | 0 | 0:01.52 | 1661928 | 0 | c57a344726 |
| PV_L2B_SamplerLaw | 53048 | 0 | 0:02.64 | 1694492 | 0 | c57a344726 |
| PV_L2B_Cursor | 53073 | 0 | 0:02.54 | 1657884 | 0 | 143889c4e8 |
| PV_L2B_EntropyTrace | 53087 | 0 | 0:02.06 | 1696472 | 0 | 5b57249d71 |
| PV_L2B_Guards | 53115 | 0 | 0:02.77 | 1900700 | 0 | 5b57249d71 |
| PV_L2B_SourceWords | 53118 | 0 | 0:00.83 | 1657188 | 0 | c4f94583a8 |
| PV_L2B_JointTransport | 53121 | 0 | 0:00.96 | 1905504 | 0 | c4f94583a8 |
| PV_L2B_AuditTrace | 53297 | 0 | 0:01.19 | 1890092 | 0 | 9a03b7e116 |
| PV_L2B_AuditStatements | 53298 | 0 | 0:01.02 | 1893588 | 0 | 9a03b7e116 |
| PV_L2B_Manifest | 53299 | 0 | 0:01.00 | 1890196 | 0 | 9a03b7e116 |

Exact target, source SHA, dependency hashes, revision, time, RSS, swap, and full axiom/error output for every attempt are in [attempts.jsonl](attempts.jsonl) and receipts/<ID>/. [validation-summary.json](validation-summary.json) records consistency checks; [ID-TALLY.json](ID-TALLY.json) retires all used/refused/preallocated IDs. The final focused manifest is not a replay of the complete frozen privacy endpoint.

One process deviation is retained: 53038 retried the aggregate reservation after about 99 seconds rather than 180. Admission passed and caps were respected. Local timestamp guards subsequently enforced the wait across Lean and Kani. No shared env-J source/object was written; the unchanged env-J executor used task-owned roots after 53000 rejected the fixed shared root.

Stopped on exhausted Lean and Kani budgets. [cleanup.json](cleanup.json) retains hashes/sizes of task-owned objects before removal. No keys or accounts were created, destroyed or cleaned up.

Next deliverable: instantiate the named honest guard invariants and E1/E2 source/environment/failed-prefix associations for this exact caller, then compose them with the same deployed RunJoin/simE coupling and existing bad events. No additional trust field or weaker observer is proposed.
