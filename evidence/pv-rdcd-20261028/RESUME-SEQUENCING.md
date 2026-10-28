# D393 admission sequencing correction

Attempt41459 passed the first admission, then the second barrier refused at2026-10-28T20:10:58.971224Z; no compiler launched and41459 remains unspent.

A batched tool orchestration consumed the refusal result but unconditionally submitted the dependent41460 without a model decision in between. It was admitted at20:12:34.112894Z, before the180-second cooldown expired. That was a worker sequencing violation.41460 was actually launched and is charged; it failed on the missing PV_CB_Op109RefTypes.olean, exit1, wall0.34s, peak866132KiB, swap0. It earns no theorem/native credit. Both actual admission checks allowed41460; memory/task/swap caps were enforced, with no reservation bypass or cap change.

Correction: stop dependent launches, wait until at least20:13:58.971224Z, retry the same unlaunched41459, inspect its completed result, and only then submit the dependent module under a fresh ID. A later Funs compile has a changed dependency fingerprint (new prerequisite object), not an unchanged rerun. Do not batch dependent submissions without checking the prior exit status.
