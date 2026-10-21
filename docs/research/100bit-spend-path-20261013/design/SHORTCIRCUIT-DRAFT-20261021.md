# Short-circuit draft — 21 October 2026

This additive packet is on `codex/cx-shortcircuit-draft-20261021`, based on
an unmerged join-split/oracle-port draft. It is not approval of the port.
No existing Lean module, S-cone candidate, M10 instrumentation or shipped
source is edited. Receipts are in `evidence/shortcircuit-draft-20261021/`.

## Stage 1: the requested prefix route has a second obstruction

`OraclePortShortCircuitCore` proves, for arbitrary oracle programs and every
oracle world, that outer short-circuit conjunction has the same verdict as
eager conjunction, has a prefix log, and has the identical full evaluation
on acceptance. These theorems keep each child program unchanged.

That last condition is material. Frozen `candidate.rs:180–195` hashes every
sorted leaf, checking a duplicate immediately; `196–200` then checks the
node count and padding; `202` calls `verify_in_place`. The latter hashes
parents level by level (`multiproof.rs:151–193`). In dV, global `Padding`
is checked before any slot; `OraclePortBatchDraft.execute` traverses a tree
recursively, and `duplicates` runs after that tree's parents. Source and
model therefore differ *inside* each child too.

`OraclePortShortCircuitObstruction.padding_not_prefix` compiles the source
ordering cut “hash a leaf, reject padding” against dV's “reject padding
without a read”. `concrete_two_not_prefix` compiles a second cut: a depth-two
binary tree with leaves at 0 and 2. Source order is leaf A, leaf B, left
parent, right parent, root. Existing `execute` order is leaf A, left parent,
leaf B, right parent, root. `two_root_eq` proves equal roots for **every**
oracle, while `two_not_prefix` proves non-prefix logs whenever the second
addresses differ. The concrete byte-address instance uses tags 0x10/0x11
versus the node tag 0x12. It is a small schedule countermodel, not a full
stored-proof reachability witness or an extracted frozen-call theorem.

Consequently an exact frozen-order decision cannot be obtained by the
requested “only skip a failing suffix” transformation of the existing dV.
No acceptance-equivalence counterexample is claimed: changing the pure
check timing/order may preserve acceptance while invalidating the prefix
argument. A frozen decision needs its own inner scheduling model and count
proof (or a read permutation/set containment proof), in addition to the
outer repair. We continue with the independent outer repair, labelled
`outerDecision`; we do not call it an exact frozen dV_sc.

S8 `compact.rs:139–144` checks successive complete 16-byte chunks and
returns on the first noncanonical value; incomplete trailing chunks are
ignored by `chunks_exact`. Its caller `candidate.rs:55` runs before
prepare (278) and batch authentication (282). These pure checks issue no
oracle reads, but their placement before the hash phases is part of any
future exact caller join. No invented trailing-length rejection is added.

Stage 1 focused checks: core attempt 3 and obstruction attempt 2, exit 0,
standard axioms only, zero swaps. Earlier failed elaborations are retained
in the manifest; they are not accepted proof evidence.

## Stage 2: outer decision and accounting

`OraclePortShortCircuitDecision.outerDecision` changes only the six-slot
outer conjunction. `decision_verdict` proves acceptance equivalence for
every stored byte string, erased prefix/message and oracle world;
`decision_prefix` proves the all-input decision-log prefix;
`decision_accepted_eq` proves identical accepted evaluations.
`OraclePortShortCircuitAccounting` lifts these to the full transcript driver.

The inherited envelopes are proved directly for this outer decision:
B_V ≤ 1161, annotated distinct reads ≤ Q+1161, decoded starts ≤ Q+1080,
and annotated issued-log length ≤ Q+2322. The annotation reruns the verifier;
its complete rejecting log need not itself be a prefix, so the length and
start results use the existing generic accounting with the proved budget.
No probability constant, padding bound, or M10 file changes.

Decision attempt 3 and accounting attempt 2 compile with standard axioms,
zero swaps; detailed source/import fingerprints and timings are recorded.

## Stage 3: conditional outer endpoint

`OraclePortShortCircuitTransport` proves identical accepted original and
annotated evaluations. `runtime_transport` uses that equality and the zero
failure mass of rejected runs to carry C7's failure bound to a runtime joined
to `outerDecision`, without requiring false all-input program equality to dV.

`OraclePortShortCircuitHeadline` defines namespace `OraclePortHeadlineDVsc`
and its `dV_sc := outerDecision`, explicitly **outer-only**, not an exact
frozen decision. Its `final_soundness` and `per_query` retain the query cap,
stored-runtime premise, numeric envelope, domain 32 ≤ Q ≤ Qmax and closed
M10 ledger. The accepted extractor experiment is `projected_sc`; the proof
transports it to C7 only after acceptance is established.

`signature-retarget.diff` records the sole textual premise-type replacement,
quoted verbatim:

```lean
(h_Rust_equals_dV : ExecutionJoin D rust)
(h_Rust_equals_dV : OuterExecutionJoin D rust)
```

These are different execution joins. **No premise deletion or strict
weakening is claimed.** The `Claims` name now resolves in the DVsc namespace;
`signature-audit.json` explicitly records the projected→projected_sc change
rather than hiding it behind equal unqualified names.

`OraclePortShortCircuitJoin.OuterOrderingJoin.model_order` targets
`verifier D outerDecision i`. Its conditional cone substitution theorem
feeds the new endpoint. `false_head_stops` and `rejected_head_log` prove that
the previous eager false-head/reading-suffix counterexample disappears at
the outer loop. They do not establish the inner child source joins.
Transport attempt 2, headline attempt 1 and join attempt 1 compile with
standard axioms only and zero swaps.

## Stage 4: handoff and audit

Pending final focused audit. Exact frozen ordering remains open.
