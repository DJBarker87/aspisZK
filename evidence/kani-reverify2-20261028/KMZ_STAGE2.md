# Stage 2 runtime windows

Kani budget exhausted exactly70/70; Rust5/5. Lean composition remains to run.

Controlled positives: typed64 inside/exterior K032–K035; iterator empty/last/interior/suffix K036–K043; clone16 K044/K045; digest heap16/16,48/48,80/96 K046–K051; roots0/0,32/32 K052–K055; actual Vec::from1736 K059/K060; query0 K061/K062 and query16 K065/K066.

No original-property counterexample occurred. Every non-timeout negative control failed exactly its deliberately wrong assertion. No control passed. All lock graphs admitted and all post-run lock hashes unchanged. Exact stub definitions and both hashes appear in every run receipt. All scopes used6G/8G/no swap/64 tasks; no overlapping own scope.

Uncredited timeouts: K011 (stage1, replaced by K030/K031); K056/K057 (combined query cases); K058 (slice-to-Vec draft); K063/K064 (queries1..15); K067/K068 (queries17..21); K069/K070 (retained1736-byte prefix/reallocation). None was rerun unchanged or with a larger cap. The actual original owned-body constructor Vec::from(array) replaces K058's stronger and expensive slice-to-Vec draft: K059/K060 passed. Query0 and16 are controlled; the two variable-index batches remain open. Direct fixed-array Vec plus truncate drafts are retained as new constructor shapes, not proof credit.

The query ranges, constructor and reallocation bottlenecks used the remaining budget before the broad arbitrary-prefix gates could be launched. Exact unrun drafts and per-row domains are in KMZ_UNRUN_SPLITS.json. Model-only proofs cannot close those runtime gaps.

Own local queues were paused to revise unrun inputs while submitted scopes finished. K035 and K058 were recovered read-only after the original SSH children exited; neither was resubmitted. K067 was already submitted when a third pause occurred, so the queue was resumed unchanged and its original receipt retained. These events are recorded in KMZ_QUEUE_*PAUSE.json.

Kani temporary files from K044 onward use attempt-owned temporary directories and are removed by the gate after timeout/completion. Final postflight will inventory remaining owned artifacts without deleting shared or persistent cache data.
