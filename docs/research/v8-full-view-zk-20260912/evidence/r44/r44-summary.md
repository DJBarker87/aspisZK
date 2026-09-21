# R44gh compact-G carry evidence

Collected logs and metadata are in this directory. The initial runner path
error is preserved in `compact-g-carry-runner-path-error-r44.log`; no reruns
were performed here and the ELF binary was not retained locally.

Lead-measured honest 100M SVM metrics: primary 18,281,174 CU; preparation
8,482,409; terminal 5,503,873; ordinary 1,277,747; full honest execution
failed at 24,907,558 CU due to the existing heap/OOM path. This regresses the
R43 best primary metric (16,456,519 CU), so R44 is not promoted as best.

The artifact/fixture hashes are recorded in `r44-artifact-sha256.txt`.

Inner timed resources: SBF build 43.91s wall / 619072 KB max RSS / exit 0;
compact-G host 29.67s / 536528 KB / exit 0; proof audit 13.09s /
459976 KB / exit 0; mutation rejection 0.00s / 3696 KB / exit 0; SVM
wrapper process 0.14s / 37628 KB / exit 0. The six SVM JSONL observations
were all execution failures (four CU-limit cases plus honest 24,907,558 CU
and bad-g-final 17,145,176 CU diagnostic failures).
