# Two-transaction frozen decision handoff

Branch `codex/cx-dv-twotx-20261021`, base `27aa8ba07`. Local stage commits;
no push or merge. Only new Lean modules, packet tools, evidence and the
requested design/join/security-contract documents changed.

## Established

`OraclePortFrozen2.dV_frozen2` authenticates batch 0, saves the ten-step
accumulator with its three digests, authenticates and resumes the saved
checkpoint with three more digests, and checks batch 1 and finish on the
returned 22-step state. Prepared context and data come from the same reached
parser/input/opening reader. No external checkpoint or prepared state is a
fixed input to the probability experiment. The C5 recurrence advance is pure;
source loop/error/field provenance remains a source join.

`acceptance_eq`, `verifier_acceptance_eq`, `original_acceptance_eq` and
`annotated_acceptance_eq` prove Boolean equivalence on the same bytes/input
and oracle. `roundtrip_log` covers authentic checkpoints even if stage 2
rejects; `accepted_trace` identifies the exact insertion point between batches.
`six_ordered_reads` proves proof/public/domain-body order in each transaction.
`verifier_six_inserted` and `annotated_twelve_inserted` distinguish the six
physical digest calls from annotation's two verifier executions.

The symbolic resource improvement retains one unit per slot on success and
rejection. Batch bounds 477 and 563 plus six checkpoint reads give terminal
1046, verifier 1161, distinct reads Q+1161 and recorded log Q+2322.
Actual-log leaf recovery, root binding, canonical rows and `checked_acceptance`
are re-established. No whole-log equality with the single-pass model is a
premise of these new consumer proofs.

`Frozen2StartChargePrefix.starts` keeps Q+34. `no_new_start` proves a submitted
transcript start already occurs in the charged prefix and has the same first
index, even if a digest input coincides with it. It does not claim arbitrary
digest bytes are disjoint from the decoder language.

`OraclePortHeadlineFrozen2PerAttempt.final_soundness` and `failure_bound` prove

```
F ≤ (Q+34)·B + κ(Q+1161) + 2^-126 + 2^-454.
```

`zero_queries` proves F ≤ 2^-100 at Q=0. `per_query` retains the original Qmax
with no positive lower bound. The extractor, B, κ, allowances and cost ledger
are unchanged. New `AcceptedRunJoin` targets the two-transaction decision;
its two accepted observations include the full ordered logs. Cone composition
is specialized to that target. Runtime binding retains its original definition.

## Validation

Every changed new module was compiled separately before its dependent bridge,
with the prescribed private object path, shared mkdir lock, Lean 4.32,
-j1 -M4400 and -DElab.async=false. The final combined import/axioms audit ran
once, after all focused targets were green:

| Target | Exit | Wall seconds | Peak RSS bytes | Swaps | Source revision |
|---|---:|---:|---:|---:|---|
| `OraclePortFrozen2Freeze` | 0 | 31.53090575011447 | 3538780160 | 0 | `98b01d4b9` |

The exact argv, full source SHA, dependency fingerprints, source revision,
exit, wall, RSS, swaps and all full `#print axioms` lines are in `manifest.json`
and each attempt directory. Final source hashes are in `frozen-sources.json`.
The union reports only `[propext, Classical.choice, Quot.sound]`. Across the
26 final modules there are 104 focused reports plus 19 repeated union reports;
peak RSS is 3639279616 bytes and every attempt records zero swaps.

Nine failed local elaboration attempts are retained and excluded from the
proof claims: namespace/type resolution and recurrence reduction in checkpoint
finish; the zero-fuel max inequality; two decision match/Boolean elaborations;
trace namespace/acceptance lookup; finite-list membership; digest-body kernel
reduction; qualified verifier unfolding; and unfolding onBytes for log-length
arithmetic. Symbolic lemmas and explicit matches/unfolding fixed them. No
memory or recursion/heartbeat cap was raised. Their recovery `sorryAx` output
is not accepted evidence; all current sources and successful reports pass the
standard-axioms audit.

```
python3 -B tools/dv-twotx/audit.py
```

This checks receipts, snapshots, current direct-import hashes, source/order
pins, new-module scope, axiom coverage and individual JSON size limits. It
runs no compiler or solver. `git diff --check` passes. No derived JSON exceeds
5 MB; no binary, object, ELF, tarball or target directory is committed.

## Retained obligations

No concrete frozen-source cone join, caller tree, inventory or runtime binding
is inhabited by this packet. The old single-pass AcceptedRunJoin is not
transported by acceptance equivalence. Required next: the assigned source
owners compose codec, prepared/accumulator provenance, allocation, query-loop,
Pool carrier/public bytes and complete frozen caller ordering into
`OraclePortFrozen2Join.AcceptedRunJoin D rust`; discharge the original
`StoredCarrierBinding`; then run the coherent frozen release replay.
The checkpoint reader/field residuals are still those in the pass-4 remainder.
The new model closes the missing checkpoint-stage interface, not those source
proofs. **The deployed security target is not yet established.**

Historical C5, frozen-slot, M9/M10, numeric and CFG dependencies were reused
from their pinned caches/evidence. This is one focused union on that base,
not a full frozen dependency rebuild. Shipped sources, protected cones and
lean-candidates are unchanged, so the conditional ELF-rebuild gate did not
trigger. No Rust/runtime suite, host build, wallet/key operation or unrelated
regression was run. Acceptance equivalence succeeded; no mathematical
counterexample is being reported.
