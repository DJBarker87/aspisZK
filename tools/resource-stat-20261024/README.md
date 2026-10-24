# ResourceStat review entrypoints

Unadopted candidate only. No scopes or consumers are created. No host capture
was taken. `baseline/` is byte-identical immutable source copied with provenance
from 25b0b9df48; its operational scripts are historical artifacts, **not review
entrypoints**. Do not execute their main functions.

From this worktree, safe offline commands are:

```
python3 -B tools/resource-stat-20261024/ResourceStat_receipt.py tests
python3 -B tools/resource-stat-20261024/ResourceStat_receipt.py audit
```

These read git objects and local files, use synthetic mocks, and write only
assigned evidence paths. Audit streams immutable objects without a historical
checkout or remote connection. No compiler/build/backend is called. A prior
unchanged successful replay need not be repeated. `sources` is an optional
primary-URL retrieval entrypoint, not a host diagnostic; its timed refresh hit
HTTP 429 and was not retried. Initial successful source hashes are preserved.

Candidate `ResourceStat_candidate.py` and `ResourceStat_go.py` retain legacy
read-only live APIs for independent inspection, but no new transport or live
measurement is supplied/run. Calling a live API is outside the offline review
commands above. These APIs confer no reservation authority.

Tests run 57 unchanged historical tests, then 57 candidate compatibility tests
with the explicit contract/schema adapters documented in FAILURES.md, plus
seven new adversarial/preservation tests. Audit supplies the exact recorded
4096 reproducer in both snapshot directions, verifies every raw shard/hash,
replays ordered legacy commands and both scans/self identities, preserves all
historical decisions, and calculates separate candidate decisions.
