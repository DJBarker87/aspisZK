# S2 interface to the lead cones, 22 October 2026

Scope: additive interface work on `codex/cx-s2-interface-20261022`, base
`4f1631685`. No shipped source or session A candidate/evidence is changed.
The release artifact pins remain default `40dc7574…`, devnet `12cb0bc2…`,
Pool `121f3e29…`. This document specifies caller obligations; it does not
claim that collecting them in a structure discharges them.

## Exact consumers

| Consumer | Required S2 input fact | Independent obligation retained |
|---|---|---|
| `CheckpointBytes5Decision.decision_success_join` | At the writer and resume positions, `MultiproofConeCanonical.bytesOf proof.val = stored` and `bytesOf public1.val = tr.statement.pubBytes`; actual writer bytes reach the resume buffer unchanged | `S1S7S8StateProvenance`, reached guard/parser/query/input/view, batch0 acceptance, successful source checkpoint execution, physical callback/content P6 interpretation |
| `CheckpointBytes5Join.S2S10CallerBinding` | The two identities above, plus `CheckpointBytes5Inputs.Oracle D hash H` | This is a per-call success implication, not a whole-history equality |
| `MultiproofConeP6Frozen2Stage.both_batches` | For **every** `b<2`, `k<3`, `bytesOf (nodes b k).val = slice parsed.wire (slotStart (3*b+k)) (32*capacity (3*b+k))` | Local parent/leaf P6 gates, and **total** law `∀ input, D.digest hash input = ok (rawOracle H input)`; arbitrary initial scratch retained |
| `S8JoinFrozenScan.parsed_y1` | Same stored proof as `parseReached`; actual compact y1 input has bytes `slice stored 7031 464` | Reached parser result; emitted scanner/physical source-carrier interpretation |
| `S7JoinQueryRows.query_rows_exact` | Query input buffers are views of the same proof; observer is None; returned mutable state is passed to the next call | Actual `PushTrace`, `Progress t 0`, output length 64, next≤22, t<22, canonical power, opening/fold/geometry and backend joins |
| `S7Kani3CallerTrace.reached_invariant` / `S8Kani2CallerJoin.finish_caller_join` | The actual reached raw/old/terms carriers are passed without substitution | `PushTrace old state sum` from S7; this derives `CallerInvariant state.raw old sum`, never from byte preservation alone |
| `S8JoinAccumulatorStage.finish_check` | Authentic raw/old inputs and their lengths | Field meaning `rawValue row = weight q rho l`; a natural-coordinate residue invariant alone is not this field meaning |
| `S8JoinS7Reference.reached_caller` | None at the logical realization | Proves only the canonical realization of the S7 reference, **not** identity with Rust raw storage |

The companion Lean module will expose the exact buffer/dispatch/account facts
and derive the concrete checkpoint, multiproof and S7/S8 caller premises.
It must not assume a source output, oracle log or observation equality.

## Quantifiers, carriers and schedule

All facts are per reached execution, with arbitrary proof bytes, public bytes,
initial scratch, accounts and digest function. Malformed/rejected executions
may reach only a prefix; no later-call existence follows from an earlier call.
Calls that are reached must preserve their arguments and earlier-call order.
The two transactions require an explicit cross-transaction retained snapshot;
within-call immutable borrowing is not proof that later transactions see the
same account bytes. Account validation, borrowing failure and ordinary errors
remain part of the caller refinement.

The admitted adapter calls are `first_decoded` at
`programs/r1-cost-probe/src/r1_pool_adapter.rs:981` and `tx2_authenticated`
at line 1020. The proof is the suffix after the 688-byte verified afterstate,
not the whole account. Stage1 uses account1's original public serialization;
Pool stage2 reconstructs it. The 320-byte ASQ8 instruction is not the
1880-byte ASF8 public serialization. Resume uses account6's verifier checkpoint,
not account2's Pool history checkpoint. Preserve the 1768-byte verifier
checkpoint across the transaction boundary; do not assume all accounts are
unchanged: stage1 writes its checkpoint, while stage2's CPI/settlement effects
belong to the Pool caller. Preserve every unmodified account field (including
lamports, owner, flags and data), and identify the allowed write footprint.

Relevant order: TX1 entry → batch0 → first ten query steps → checkpoint write;
TX2 entry → resume → batch1 → remaining twelve query steps → finish.
Within each batch the tree kinds are 0,1,2, with short-circuit rejection.
Within checkpoint save/resume, each digest order is proof, public, checksum;
these six oracle reads are a **conclusion** of the checkpoint cone. S2 supplies
argument provenance/order/None, not an assumed six-read log.

None-passing must use the actual `Option<fn(Phase)>` callback carrier (or a
proved representation map), under release observer-off configuration. A
Boolean saying “observer off” does not identify that Option. Backend tracing
inside S7 needs its own callback/carrier join. The proposed Lean record keeps
the observer carrier polymorphic so it does not invent a callback ABI.

## Read-only cross-check against available session A statements

The available S2 packet is `design/S2-KANI-20261021.md`,
`tools/s2-kani-20261021/`, and `evidence/s2-kani-20261021/`.
Its `callers-v3` child-boundary checks establish dispatch addresses/lengths,
semantic token, split index, observer presence, child failures and order.
Its own text explicitly leaves the AccountInfo/adapter cone untranslated.
Its parser-v1 proves caller addresses/error propagation, not buffer validity;
opening shell byte/state checks are separate and leave backend/hash binding
open. These are compatible local statements, not an inhabitant of the above
caller interface. The 21 October header fixture's zero suffix is not a
universal proof-buffer preservation theorem.

At inspection, neither the assigned checkout nor the root checkout's
`lean-candidates`/S2 evidence contained the reported new SDK 10/15-window
packet. Its location was requested from the lead. The 10/15 status is therefore
user-reported, not independently verified here. Do not silently promote it
to a universal same-byte theorem. Pending direct inspection, the remaining
mismatches are: (1) address/length vs byte contents; (2) independently successful
windows vs the complete reached-call domain; (3) within-transaction vs retained
cross-transaction snapshot; (4) U8 slices vs `List (Fin 256)` via `bytesOf`;
(5) total multiproof oracle law vs success-conditioned checkpoint law;
(6) logical S7 reference vs actual raw accumulator; (7) observer token vs real
callback Option; (8) permitted account effects vs blanket preservation.

## Trust and adoption boundary

No public field may be a free `Prop` chosen by the instantiator, a whole-call
result equality, oracle-history equality, accepted observation equality, or a
claim that the source already equals `dV_frozen2`. Arithmetic provenance is
kept outside `S2CallerFacts`; collecting it is not proving it. The interface
is conditional organization plus checked composition. Instantiating S2,
remaining S7/S8/P6/source/Pool joins, both raw/annotation passes, and a coherent
release replay still remain before the 100-bit target is established.
