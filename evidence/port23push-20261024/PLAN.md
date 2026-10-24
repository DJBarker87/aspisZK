# Port23PUSH exact mutable push design

Assigned base 3166426e45d8c1eb2ce8b6201f7198c0536aa2c5, branch
codex/cx-port23push-20261024. Only new job-prefixed tools, evidence and modules.
No shipped changes, merge/push, allocator job, backend or release replay.

Producer: include immutable base verifier.rs lines 204 (BatchedWeights carrier),
217-220 (actual mutable push), 230-247 (residue/power access and row update),
and full unchanged field.rs/wide_exact.rs. Supply enclosing impl braces only.
A job-only free function directly calls the unchanged inherent method, recovering
ordered reachability without replacing its body. Source audit records whole-file
and span hashes. Inputs retain arbitrary raw Vec, terms, power and M31 word.
No canonicality, overflow or index restriction is silently installed.

Extract Charon once and Aeneas once, each independently capped
High1536MiB/Max2GiB/Swap0/Tasks64. Reuse reviewed Port21 scanner including pidfd
TOCTOU fix; fresh preflight/go and in-scope snapshots must admit reservations
below 55GiB with 7GiB OS reserve. Tool/sysroot/source pins checked before/after.
Expected time: selected optimized compilation/extraction, no arithmetic gate.

Compare complete emitted Result (including fail/div) and mutable back closures
with S7Kani2OwnedPush.push_owned, retaining every Vec element and terms. First
prove symbolic loop/closure shapes, then smallest local theorem, dependent row
consumer if justified, then full statement/axiom audit. Never infer effects from
Result equality. Inspect exact fixed primitive graph and D157/D189 policy scope;
if a leaf interpretation is missing, record its literal boundary and stop that
claim rather than inventing noHash or trusting desired equality.

Budget: Lean at most13 new invocations, extraction at most2 total new invocations,
Kani0, standalone Rust0, backend0, full frozen manifest0. Own ledger only; global
entry320/368 and 22 remain unassigned, no ceiling/reset inference. New validation
and reused source/evidence distinguished; both deployed targets not established.
