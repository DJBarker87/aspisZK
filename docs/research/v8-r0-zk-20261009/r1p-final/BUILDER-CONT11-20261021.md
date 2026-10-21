# Builder continuation 11

Branch `codex/cx-builder-ref11-20261021`, base `4715dbaf3`.

## Scope

Repair the forest callback state ABI, then attempt semantic admission and the
destructor pointer/iterator correspondence. RuntimeJoin and checker/retry
coupling remain named execution joins. No concurrent-worker file is edited.

Only J9396–J9399 remain unused in the assigned attempt range. Earlier attempts
9200–9395 have host receipts and will not be reused.

## Stage 1: callback adapter

`BuilderForestCallbackAdapter` proves state/pair round trips, successful
borrow-back application, captured-index restoration and tuple-call adaptation.
The returned callback is `back next`, never the original environment. This
supplies a generic checked adapter; it does not yet certify the aggregate
forest or its source identification. J9396: exit 0, wall 1.17 s, peak RSS
2,532,764 KiB, swap 0. Five axiom audits: three use only `propext`, two none.
Exact source revision/hash, dependency fingerprint and logs are retained in
`builder-cont11-attempts.jsonl`.
