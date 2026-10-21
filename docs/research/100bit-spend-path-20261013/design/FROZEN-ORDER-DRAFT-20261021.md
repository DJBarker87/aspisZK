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

`OraclePortFrozenOrderDecision.dV_frozen` keeps admission, reached parsing,
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

Collision-free recovery is in progress over actual levels; unconditional
recovery-table permutation remains false on the inherited collision witness.

## Stage 3: headline and join split

Pending. No premise removal or new headline is claimed before C6 is proved.

## Evidence

`evidence/frozen-order-draft-20261021/manifest.json` records every local
attempt, source revision/hash, direct-import fingerprint, exact command,
exit, wall time, peak RSS, swaps, errors and complete axiom reports.
The launcher uses the prescribed shared mkdir lock and private object path.
No package build, frozen release replay, source re-pin, wallet action, push
or merge is performed.
