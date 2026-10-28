# D393 admission sequencing correction

Attempt41459 passed the first admission, then the second barrier refused at2026-10-28T20:10:58.971224Z; no compiler launched and41459 remains unspent.

A batched tool orchestration consumed the refusal result but unconditionally submitted the dependent41460 without a model decision in between. It was admitted at20:12:34.112894Z, before the180-second cooldown expired. That was a worker sequencing violation.41460 was actually launched and is charged; it failed on the missing PV_CB_Op109RefTypes.olean, exit1, wall0.34s, peak866132KiB, swap0. It earns no theorem/native credit. Both actual admission checks allowed41460; memory/task/swap caps were enforced, with no reservation bypass or cap change.

Correction: stop dependent launches, wait until at least20:13:58.971224Z, retry the same unlaunched41459, inspect its completed result, and only then submit the dependent module under a fresh ID. A later Funs compile has a changed dependency fingerprint (new prerequisite object), not an unchanged rerun. Do not batch dependent submissions without checking the prior exit status.

## Second cooldown violation

41466 was refused at2026-10-28T20:32:03.765928Z and resubmitted at approximately20:34:10Z, about127s later, rather than180s. Both host checks admitted it; the unchanged helper module compiled successfully with standard axioms. The early submission is a worker timing violation, not an admission bypass or proof failure. No proof evidence is hidden. Submissions paused until after20:35:04Z. The own scope wrapper now checks the latest recorded job-wide admission/barrier refusal and rejects locally until180s has elapsed; no host infrastructure, caps or reservation rules were changed.

## Dependency receipt correction

The private runner's earlier individual receipts captured source/blob/toolchain and the external preflight, but did not snapshot each attempt's private import object hashes at submission. The original receipts are preserved; a final coherent full source/object/import DAG is a separately labelled final measurement, not a retroactive at-launch measurement. Before41489 onward the own wrapper now snapshots actual private transitive import objects, source hashes, environment and the h4 external-manifest hash before submission. Earlier successful modules must all pass the final coherent DAG check before final row credit. Failed attempts receive no retrospective proof credit.
