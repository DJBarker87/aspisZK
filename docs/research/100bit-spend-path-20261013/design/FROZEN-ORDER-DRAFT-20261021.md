# Frozen-order model port draft — 21 October 2026

Unmerged branch `codex/cx-frozen-order-draft-20261021`. User approval of the
port is required before merge. Existing Lean modules, S-cone candidate pins,
M10 instrumentation, and production Rust remain read-only.

## Stage 1: exact slot schedule and decision

`OraclePortFrozenOrderSlot` copies the inspected inner-order draft into a
new namespace, `AspisR1.OraclePortFrozenOrder`. Inspection found its schedule
already matches the binary source: `candidate.rs:92–113` sorts keys by
(index, position); `:173–195` hashes every sorted leaf and immediately
checks duplicate digests; `:196–205` counts nodes, checks whole-word zero
padding, then calls `verify_in_place`. `multiproof.rs:151–213` traverses
ascending levels and ascending occupied parent indices, consuming proof
siblings consecutively. Paths are relative to `crates/aspis-r1-cost-probe/src/`.
The list runner reads each live group before constructing its next prefix;
this models the source's safe in-place overwrite order.

`OraclePortFrozenOrder.dV_frozen` (`OraclePortFrozenOrderDecision.lean`) keeps admission, reached parsing,
query extraction, six-slot short circuit and the existing arithmetic check.
It removes the global recursive-tree `Padding` precheck: the frozen source
checks each slot's padding after hashing its leaves. Keeping that old guard
would preserve a rejection-order mismatch. The per-slot width test totalizes
short unreachable slices; source caller reachability is still a refinement
obligation. This packet does not claim an extracted Rust theorem.

## Stage 2: recovery and accounting

The actual source-order program now has compiled all-input bounds:
`decision_budget` ≤ 1046, `verifier_bound` ≤ 1161, `distinct_bound` ≤ Q+1161,
`starts_bound` ≤ Q+1080, and `log_length` ≤ Q+2322. No comparison to a
recursive log is used. `level_conservation` and `levels_conservation` prove
symbolically that parent calls plus the remaining frontier/proof weight are
bounded by initial live nodes plus proof words. `leaves_bound` covers early
duplicate rejection. Six slots consume at most 2·66+914 = 1046 calls; this
includes a conservative six-call slack compared with the recursive 1040.

`level_lift` and `levels_path` construct the exact indexed authentication
path by induction over executed levels. `leaves_retained` includes every
sorted source position, including duplicates; successful duplicate checks
suffice to retain its digest. `slot_path` proves the root equation and
containment of its complete leaf/parent trace in the actual frozen slot log.
`recovery_at_index` applies the original collision-free first-commitment-cut
recovery theorem to that witness. `authenticated` recovers each of the 22
source openings at its exact index, through the accepted six-slot short
circuit. This neither permutes logs nor adds independent path hashes.
Unconditional recovery-table permutation remains false on the inherited
collision witness.

`OraclePortFrozenOrderC6.checked_acceptance` compiles at the actual adaptive
stored experiment and `dV_frozen`, with no source-data, recovery, reader,
matching, writer or backend model premise. Its interface is verbatim:

```lean
def checked_acceptance (D : LiteralByteProtocol.Decoder) (P : Prover) (Q : Nat)
    (hq : ∀ H : Bytes → State, (eval H P).1.length ≤ Q) :
    OraclePortStoredChecksC4.CheckedAcceptance D decision (canon P) (Q+1161)
```

Here `decision` is the abbreviation for `OraclePortFrozenOrder.dV_frozen`
in `OraclePortFrozenOrderReached`. New reached-run/root/actual/canonical
modules redo the dependent C6 steps. Existing parsing, typed arithmetic,
row restoration, frame grammar and observation transport lemmas are reused
without changing their definitions. The collision predicate and canonical
prover are unchanged.

## Stage 3: headline and join split

The new conditional endpoint is
`OraclePortHeadlineFrozen.final_soundness`, in
`OraclePortFrozenOrderHeadline.lean`; `per_query` also compiles. It retains
the accepted extractor cost, returned relation, abort allowance and runtime
bound, with the accepted experiment now fixed to `dV_frozen`. The per-query
form applies for 32 ≤ Q ≤ Qmax, as in the inherited AccLog draft.

The sole source-verifier premise is the following structure in namespace
`OraclePortFrozenOrderJoin`, quoted verbatim:

```lean
structure AcceptedRunJoin (D : LiteralByteProtocol.Decoder) (rust : Verifier) : Prop where
  verifier : AcceptedVerifierJoin rust (verifier D OraclePortFrozenOrder.dV_frozen)
  annotated : ∀ (P : Prover) H,
    (eval H (annotatedWith D rust P)).2.2 = true →
      eval H (annotatedWith D rust P) =
        eval H (annotated D OraclePortFrozenOrder.dV_frozen P)
```

Here `AcceptedVerifierJoin` is verbatim:

```lean
def AcceptedVerifierJoin (source model : Verifier) : Prop :=
  ∀ H i, (eval H (source i)).2 = true → eval H (source i) = eval H (model i)
```

Ordered logs, all return values, stored/public data, recovered words and both
annotation passes are retained. `StoredCarrierBinding D rust P runtime`
remains a separate runtime premise. `total_join_accepted` supplies the join
from total equality at this same frozen model. The generic cone composition
rules now target the frozen decision; total `PerConeJoins`, S10 inventory and
source/model caller identities imply the two-pass join without an additional
source-stability hypothesis. The evaluation-only cone route retains its
explicit sufficient enrichment-stability obligation.

`OraclePortFrozenOrderConsumer` and `OraclePortFrozenOrderProbability`
re-establish the clean adaptive consumer and collision/start failure bound.
`OraclePortFrozenOrderTransport` transports the actual extractor input and
runtime failure mass using accepted equality, without comparison to the old
recursive log. The cached closed M10 ledger is consumed read-only.

The exact resolved signature diff against the inherited AccLog endpoint is
recorded in `evidence/frozen-order-draft-20261021/headline-signature.diff`.
It exposes only the two fixed-model substitutions: the `AcceptedRunJoin`
namespace and the `Claims` namespace. This is a model retargeting, **not a
claim that the new source join is weaker than the old join at a different
model**, and not a premise deletion from R19. R19's free decision and boundary
premises remain untouched. No premise is removed in this packet. The accepted
interface retains the inherited logical shape rather than adding recovery,
budget, C6 or model-soundness assumptions.

The join delivery table in `JOIN-SPLIT-DRAFT-20261021.md` now names
`dV_frozen` at its model boundary. Concrete S-cone inhabitants, exact mutable
array/byte adapters, the full frozen caller tree and both caller identities
remain source-owner work. Matching the model's inner schedule removes the
old requirement to prove literal accepted-log equality against recursive
postorder; it does not itself prove an extracted source refinement.

## Evidence

`evidence/frozen-order-draft-20261021/manifest.json` records every local
attempt, source revision/hash, direct-import fingerprint, exact command,
exit, wall time, peak RSS, swaps, errors and complete axiom reports.
The launcher uses the prescribed shared mkdir lock and private object path.
No package build, frozen release replay, source re-pin, wallet action, push
or merge is performed.


## Delivery boundary

All requested model-side stages are proved in additive new modules. The
conditional headline does not establish that the deployed/frozen verifier
inhabits its source join, nor that a runtime satisfies the carrier binding.
No full frozen release replay or deployment is claimed. A coherent release
closure still needs the dedicated build-host workflow. The branch remains a
draft for lead review and cannot be merged before user approval of the port.
