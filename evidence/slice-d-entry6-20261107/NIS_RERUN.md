# Isolated native reruns

Original configuration SHA256 is retained byte-exactly; relocated serialized configurations have distinct hashes because source/output/temporary paths change. Native flags, features, harness names, property, source snapshots, optimizer and timeouts are identical. Explicit CARGO_TARGET_DIR and --target-dir agree inside NIS workspace; predecessor target is never reused.

| NIS | Original | Old target | New target | Result | Kind |
|---|---|---|---|---|---|
| NIS_K001 | NHY_K051 | `/home/dombarker/project-offloads/codex-cx-slice-d-entry4-20261106/NHY_target` | `/home/dombarker/project-offloads/codex-cx-slice-d-entry6-20261107/NIS_target` | 0 / reproduced | pass |
| NIS_K002 | NHY_K052 | `/home/dombarker/project-offloads/codex-cx-slice-d-entry4-20261106/NHY_target` | `/home/dombarker/project-offloads/codex-cx-slice-d-entry6-20261107/NIS_target` | 1 / reproduced | matched failing control |
| NIS_K003 | NHY_K055 | `/home/dombarker/project-offloads/codex-cx-slice-d-entry4-20261106/NHY_target` | `/home/dombarker/project-offloads/codex-cx-slice-d-entry6-20261107/NIS_target` | 0 / reproduced | pass |
| NIS_K004 | NHY_K056 | `/home/dombarker/project-offloads/codex-cx-slice-d-entry4-20261106/NHY_target` | `/home/dombarker/project-offloads/codex-cx-slice-d-entry6-20261107/NIS_target` | 1 / reproduced | matched failing control |
| NIS_K005 | NHY_K059 | `/home/dombarker/project-offloads/codex-cx-slice-d-entry4-20261106/NHY_target` | `/home/dombarker/project-offloads/codex-cx-slice-d-entry6-20261107/NIS_target` | 0 / reproduced | pass |
| NIS_K006 | NHY_K060 | `/home/dombarker/project-offloads/codex-cx-slice-d-entry4-20261106/NHY_target` | `/home/dombarker/project-offloads/codex-cx-slice-d-entry6-20261107/NIS_target` | 1 / reproduced | matched failing control |
| NIS_K007 | NHY_K095 | `/home/dombarker/project-offloads/codex-cx-slice-d-entry4-20261106/NHY_target` | `/home/dombarker/project-offloads/codex-cx-slice-d-entry6-20261107/NIS_target` | 0 / reproduced | pass |
| NIS_K008 | NHY_K096 | `/home/dombarker/project-offloads/codex-cx-slice-d-entry4-20261106/NHY_target` | `/home/dombarker/project-offloads/codex-cx-slice-d-entry6-20261107/NIS_target` | 1 / reproduced | matched failing control |
| NIS_K009 | NHY_K108 | `/home/dombarker/project-offloads/codex-cx-slice-d-entry4-20261106/NHY_target` | `/home/dombarker/project-offloads/codex-cx-slice-d-entry6-20261107/NIS_target` | 0 / reproduced | pass |
| NIS_K010 | NHY_K109 | `/home/dombarker/project-offloads/codex-cx-slice-d-entry4-20261106/NHY_target` | `/home/dombarker/project-offloads/codex-cx-slice-d-entry6-20261107/NIS_target` | 1 / reproduced | matched failing control |
| NIS_K011 | NIJ_K056 | `/home/dombarker/project-offloads/codex-cx-slice-d-entry4-20261106/NHY_target` | `/home/dombarker/project-offloads/codex-cx-slice-d-entry6-20261107/NIS_target` | 0 / reproduced | pass |
| NIS_K012 | NIJ_K057 | `/home/dombarker/project-offloads/codex-cx-slice-d-entry4-20261106/NHY_target` | `/home/dombarker/project-offloads/codex-cx-slice-d-entry6-20261107/NIS_target` | 1 / reproduced | matched failing control |
| NIS_K013 | NIJ_K070 | `/home/dombarker/project-offloads/codex-cx-slice-d-entry4-20261106/NHY_target` | `/home/dombarker/project-offloads/codex-cx-slice-d-entry6-20261107/NIS_target` | 0 / reproduced | pass |
| NIS_K014 | NIJ_K071 | `/home/dombarker/project-offloads/codex-cx-slice-d-entry4-20261106/NHY_target` | `/home/dombarker/project-offloads/codex-cx-slice-d-entry6-20261107/NIS_target` | 1 / reproduced | matched failing control |
| NIS_K015 | NIJ_K073 | `/home/dombarker/project-offloads/codex-cx-slice-d-entry4-20261106/NHY_target` | `/home/dombarker/project-offloads/codex-cx-slice-d-entry6-20261107/NIS_target` | 0 / reproduced | pass |
| NIS_K016 | NIJ_K074 | `/home/dombarker/project-offloads/codex-cx-slice-d-entry4-20261106/NHY_target` | `/home/dombarker/project-offloads/codex-cx-slice-d-entry6-20261107/NIS_target` | 1 / reproduced | matched failing control |
| NIS_K017 | NIJ_K075 | `/home/dombarker/project-offloads/codex-cx-slice-d-entry4-20261106/NHY_target` | `/home/dombarker/project-offloads/codex-cx-slice-d-entry6-20261107/NIS_target` | 0 / reproduced | pass |
| NIS_K018 | NIJ_K076 | `/home/dombarker/project-offloads/codex-cx-slice-d-entry4-20261106/NHY_target` | `/home/dombarker/project-offloads/codex-cx-slice-d-entry6-20261107/NIS_target` | 1 / reproduced | matched failing control |
| NIS_K019 | NIJ_K077 | `/home/dombarker/project-offloads/codex-cx-slice-d-entry4-20261106/NHY_target` | `/home/dombarker/project-offloads/codex-cx-slice-d-entry6-20261107/NIS_target` | 0 / reproduced | pass |
| NIS_K020 | NIJ_K078 | `/home/dombarker/project-offloads/codex-cx-slice-d-entry4-20261106/NHY_target` | `/home/dombarker/project-offloads/codex-cx-slice-d-entry6-20261107/NIS_target` | 1 / reproduced | matched failing control |
| NIS_K021 | NIJ_K079 | `/home/dombarker/project-offloads/codex-cx-slice-d-entry4-20261106/NHY_target` | `/home/dombarker/project-offloads/codex-cx-slice-d-entry6-20261107/NIS_target` | 0 / reproduced | pass |
| NIS_K022 | NIJ_K080 | `/home/dombarker/project-offloads/codex-cx-slice-d-entry4-20261106/NHY_target` | `/home/dombarker/project-offloads/codex-cx-slice-d-entry6-20261107/NIS_target` | 1 / reproduced | matched failing control |
| NIS_K023 | NIJ_K081 | `/home/dombarker/project-offloads/codex-cx-slice-d-entry4-20261106/NHY_target` | `/home/dombarker/project-offloads/codex-cx-slice-d-entry6-20261107/NIS_target` | 0 / reproduced | pass |
| NIS_K024 | NIJ_K082 | `/home/dombarker/project-offloads/codex-cx-slice-d-entry4-20261106/NHY_target` | `/home/dombarker/project-offloads/codex-cx-slice-d-entry6-20261107/NIS_target` | 1 / reproduced | matched failing control |
| NIS_K025 | NIJ_K083 | `/home/dombarker/project-offloads/codex-cx-slice-d-entry4-20261106/NHY_target` | `/home/dombarker/project-offloads/codex-cx-slice-d-entry6-20261107/NIS_target` | 0 / reproduced | pass |
| NIS_K026 | NIJ_K084 | `/home/dombarker/project-offloads/codex-cx-slice-d-entry4-20261106/NHY_target` | `/home/dombarker/project-offloads/codex-cx-slice-d-entry6-20261107/NIS_target` | 1 / reproduced | matched failing control |
| NIS_K027 | NIJ_K085 | `/home/dombarker/project-offloads/codex-cx-slice-d-entry4-20261106/NHY_target` | `/home/dombarker/project-offloads/codex-cx-slice-d-entry6-20261107/NIS_target` | 0 / reproduced | pass |
| NIS_K028 | NIJ_K086 | `/home/dombarker/project-offloads/codex-cx-slice-d-entry4-20261106/NHY_target` | `/home/dombarker/project-offloads/codex-cx-slice-d-entry6-20261107/NIS_target` | 1 / reproduced | matched failing control |
| NIS_K029 | NIJ_K087 | `/home/dombarker/project-offloads/codex-cx-slice-d-entry4-20261106/NHY_target` | `/home/dombarker/project-offloads/codex-cx-slice-d-entry6-20261107/NIS_target` | 0 / reproduced | pass |
| NIS_K030 | NIJ_K088 | `/home/dombarker/project-offloads/codex-cx-slice-d-entry4-20261106/NHY_target` | `/home/dombarker/project-offloads/codex-cx-slice-d-entry6-20261107/NIS_target` | 1 / reproduced | matched failing control |
| NIS_K031 | NIJ_K089 | `/home/dombarker/project-offloads/codex-cx-slice-d-entry4-20261106/NHY_target` | `/home/dombarker/project-offloads/codex-cx-slice-d-entry6-20261107/NIS_target` | 0 / reproduced | pass |
| NIS_K032 | NIJ_K090 | `/home/dombarker/project-offloads/codex-cx-slice-d-entry4-20261106/NHY_target` | `/home/dombarker/project-offloads/codex-cx-slice-d-entry6-20261107/NIS_target` | 1 / reproduced | matched failing control |
| NIS_K033 | NIJ_K091 | `/home/dombarker/project-offloads/codex-cx-slice-d-entry4-20261106/NHY_target` | `/home/dombarker/project-offloads/codex-cx-slice-d-entry6-20261107/NIS_target` | 0 / reproduced | pass |
| NIS_K034 | NIJ_K092 | `/home/dombarker/project-offloads/codex-cx-slice-d-entry4-20261106/NHY_target` | `/home/dombarker/project-offloads/codex-cx-slice-d-entry6-20261107/NIS_target` | 1 / reproduced | matched failing control |
| NIS_K035 | NIJ_K093 | `/home/dombarker/project-offloads/codex-cx-slice-d-entry4-20261106/NHY_target` | `/home/dombarker/project-offloads/codex-cx-slice-d-entry6-20261107/NIS_target` | 0 / reproduced | pass |
| NIS_K036 | NIJ_K094 | `/home/dombarker/project-offloads/codex-cx-slice-d-entry4-20261106/NHY_target` | `/home/dombarker/project-offloads/codex-cx-slice-d-entry6-20261107/NIS_target` | 1 / reproduced | matched failing control |
| NIS_K037 | NIJ_K095 | `/home/dombarker/project-offloads/codex-cx-slice-d-entry4-20261106/NHY_target` | `/home/dombarker/project-offloads/codex-cx-slice-d-entry6-20261107/NIS_target` | 0 / reproduced | pass |
| NIS_K038 | NIJ_K096 | `/home/dombarker/project-offloads/codex-cx-slice-d-entry4-20261106/NHY_target` | `/home/dombarker/project-offloads/codex-cx-slice-d-entry6-20261107/NIS_target` | 1 / reproduced | matched failing control |
| NIS_K039 | NIJ_K097 | `/home/dombarker/project-offloads/codex-cx-slice-d-entry4-20261106/NHY_target` | `/home/dombarker/project-offloads/codex-cx-slice-d-entry6-20261107/NIS_target` | 0 / reproduced | pass |
| NIS_K040 | NIJ_K098 | `/home/dombarker/project-offloads/codex-cx-slice-d-entry4-20261106/NHY_target` | `/home/dombarker/project-offloads/codex-cx-slice-d-entry6-20261107/NIS_target` | 1 / reproduced | matched failing control |
| NIS_K041 | NIJ_K099 | `/home/dombarker/project-offloads/codex-cx-slice-d-entry4-20261106/NHY_target` | `/home/dombarker/project-offloads/codex-cx-slice-d-entry6-20261107/NIS_target` | 0 / reproduced | pass |
| NIS_K042 | NIJ_K100 | `/home/dombarker/project-offloads/codex-cx-slice-d-entry4-20261106/NHY_target` | `/home/dombarker/project-offloads/codex-cx-slice-d-entry6-20261107/NIS_target` | 1 / reproduced | matched failing control |
| NIS_K043 | NIJ_K101 | `/home/dombarker/project-offloads/codex-cx-slice-d-entry4-20261106/NHY_target` | `/home/dombarker/project-offloads/codex-cx-slice-d-entry6-20261107/NIS_target` | 0 / reproduced | pass |
| NIS_K044 | NIJ_K102 | `/home/dombarker/project-offloads/codex-cx-slice-d-entry4-20261106/NHY_target` | `/home/dombarker/project-offloads/codex-cx-slice-d-entry6-20261107/NIS_target` | 1 / reproduced | matched failing control |
| NIS_K045 | NIJ_K109 | `/home/dombarker/project-offloads/codex-cx-slice-d-entry4-20261106/NHY_target` | `/home/dombarker/project-offloads/codex-cx-slice-d-entry6-20261107/NIS_target` | 1 / reproduced | matched failing control |

Exact original hashes and section6 resource/source records: NIS_RERUN.json, NIS_ATTEMPTS.jsonl and per-attempt receipts. Zero rows admitted before the canonical combined import / raw-axiom / NFX gate.
