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

Pending focused verification.

## Stage 3: conditional outer endpoint

Pending focused verification. No premise removal is claimed.

## Stage 4: handoff and audit

Pending final focused audit. Exact frozen ordering remains open.
