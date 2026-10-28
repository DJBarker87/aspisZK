# Stage 1: scalar cut and iterator predecessors

Exact results: K001 scalar opening endpoints, K003 arbitrary832-byte range,
K004 key iterator, K005 zero key array, K006 sort iterator, K007 padding iterator,
K008 zero leaf scratch passed. K002 large-offset single-byte range timed out;
K009 combined paired row timed out. Neither failed shape is rerun; replacement
families are fixed physical positions and one-window rows respectively.
All Kani runs have frozen-graph receipts, offline execution and unchanged lock.
No LPb passing stage used. No field multiplication, SHA implementation or stub.

L002 accepts NBJ_Opening.address_bounds and selected_leaf (the latter consumes
NBI_Views read-only), standard axioms only. L001/L003 rejected drafts excluded.
Source snapshot of each rejected draft retained. Section6 attempt fields are
in per-attempt receipt.json and NBJ_ATTEMPTS.json. See NBJ_SCOPE_EXCEPTION.md
for the first two scopes' scheduling violation; no all-serial claim is made.

All498 local frozen source/root Cargo files match revision4bb3b3f5. No repository
harness changed. ELF rebuild not triggered; inherited release pins retained.
S2, all three complete authentication units and deployed100-bit target remain
OPEN. No headline premise removed and no new trust assumption introduced.
