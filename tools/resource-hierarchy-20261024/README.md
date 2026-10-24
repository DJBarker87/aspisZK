# ResourceHierarchy: unadopted offline accounting assessment

Run the full nonmutating audit from any directory:

```
python3 -B /Users/dominic/ZK/.worktrees/cx-resource-hierarchy/tools/resource-hierarchy-20261024/ResourceHierarchy_audit.py
```

It emits JSON on stdout and focused test results on stderr. It reads historical
source/evidence only via immutable git 5756082d85e4d6784de4566059d6a9845604342a.
An audit hook refuses network, real directory scans, filesystem writes, and
commands other than the git object reader. Mocked historical commands are
compared in order; none execute. It does not allocate or launch a consumer.
Candidate/GO are concrete copies of the reviewed source with explicit namespace,
schema, accounting diagnostics/exception, and disabled public live-admission
boundary. Old source is never edited or silently loaded from a live worktree.

`ResourceHierarchy_receipt.py LABEL` captures stdout/stderr in new files and a
wait4 receipt. Existing labels cannot be overwritten. `LABEL sources` instead
runs the separately authorized local primary-reference fetch (network only to
primary source URLs; no host). Only hashes, sizes and symbol lines are retained.
The full audit itself never fetches sources or writes files.

Read evidence/resource-hierarchy-20261024/CRITERIA.md (committed before code),
SOURCE-ASSESSMENT.md, FAILURES.md and REPORT.md. Candidate policy is not adopted.
Every apparent acceptance is an offline estimate, never current admission/GO.
No lower-cap runtime recommendation follows from these observations.
