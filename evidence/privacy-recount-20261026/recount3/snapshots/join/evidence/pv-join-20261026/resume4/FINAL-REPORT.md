# pv-join4 final report

Branch `codex/pv-join-20261026`, base `1ad24470b8`. Target not yet established.
No endpoint premise was removed, weakened, added, or changed. The endpoint's
before/after statement and deployment conditions are identical.

## Stop: checked unrestricted op121 P6 ROW counterexample

The proposed ROW is equality of shipped
`evaluate_state_only_polynomial` and the existing Horner reference, for every
raw `[QM31;28]` polynomial and `QM31` challenge. With coefficient 2 equal to
`[1,0,0,0]`, all other coefficients zero, and challenge `[0,2147483648,0,0]`,
the optimized native source returns `[3,0,0,0]`, while the reference returns
`[2147483646,0,0,0]`. All host aspis-core Rust bytes match this worktree.

Kani confirms a source unsigned subtraction overflow at `field.rs:331`;
the separate reference-only harness passes all 134 checks with its exact
output. `--no-overflow-checks` still retains the MIR assertion and also fails;
no successful Kani wrapping-semantics proof is claimed. This is a checked
counterexample to this proposed P6 source/reference ROW, not to source
self-equality with its own extraction, admitted fixtures, or privacy.
No source fix or canonical-input restriction was introduced.

Per the user's stop rule, substantive work stopped on this counterexample.
Lean: **5/100**, IDs **36800–36804**, never reused, next unused **36805**;
95 attempts unspent under that exception. Kani: **6/6**, three passed,
two arithmetic-failure reports, one timeout. Harnesses were listed first.
The timed-out 1024-row scan was not rerun. No local Lean compilation.

## Reachability, source rows, and fixtures

For transfer and withdrawal: **execution-reached sets unresolved; entries
proved unreachable on all admitted inputs: empty**. Every inventory entry has
a static dependency path, but that is not an execution witness.
`PV_Join_PublicFailure4.fail_public` proves one actual extracted rejection
prefix: a public-serialization panic makes the complete attempt panic before
its continuation. Its hypothesis is not established universally for either
fixture; no row is excluded using it.

Inventory **30 → 30**: zero new source laws; zero entries universally excluded
from both fixtures. Six native-effect entries **4, 32, 122, 123, 232, 257** are
explicitly deferred to pv-runjoin, with exact reasons in `inventory.json`;
24 other entries remain unresolved, including the failed op121 P6 candidate.
cb4's op259 declaration remains PREPARED; no duplicate law or credit is taken.

Both proof-byte equations, full audit/status, V163 and native non-vacuity stay
open. Their exact equations are retained in `fixture-obligations.json`.
rw20 was checked at start, stage end and final: no concrete protocol-to-model
instance was published. No competing instance was built.

## Final audit and receipts

The last three Lean attempts are the two statement/axioms portions and the
combined audit. All 127 PV_Join theorems plus headline pass, standard axioms
only. This reuses the inherited cache; it is not a clean release replay.

| Target | ID | Exit | Wall | Peak RSS KiB | Swap | Revision |
|---|---:|---:|---|---:|---:|---|
| FinalAudit4A | 36802 | 0 | 0:03.19 | 4344036 | 0 | 6386cb7f6d |
| FinalAudit4B | 36803 | 0 | 0:02.84 | 4348372 | 0 | 6386cb7f6d |
| CombinedAudit4 | 36804 | 0 | 0:01.73 | 4338864 | 0 | 6386cb7f6d |

`receipt-index.json` retains every target, exit, wall, RSS, swap, source
revision/hash, dependency fingerprint and full axioms output. The timed-out
scan's wrapper time report misses child peak RSS: exact peak is unavailable;
a live CBMC sample was 3,445,352 KiB. This limitation is explicit in its
receipt; it earns no source-law credit. All observed swaps are zero.

No shipped source, key, sibling worktree, or launcher was changed. The new
native Cargo target cache was removed; the pinned Lean cache is retained.
Commits before this final evidence commit are in `commits.txt`.

Next deliverable: lead review of the failed unrestricted op121 P6 row and
its raw-input semantics; rw20's concrete model instance, then transfer and
withdrawal byte equations with actual execution reachability receipts.
