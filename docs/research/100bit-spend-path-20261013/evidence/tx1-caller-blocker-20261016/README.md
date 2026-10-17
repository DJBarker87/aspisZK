# Exact actual tx1 emission blocker and untested helper proposal

The isolated C branch was rebased onto `3da1531fc` and cherry-picked only the lead-approved Prepared source `3335eecf2f2a08096abe95c67ac6b304f2df6284` (local equivalent `73906556a`). No live worktree, runtime harness or SBF job was touched. No Lean was launched.

The actual `verifier::tx1` body is retained completely and byte-identically (SHA256 `367d4e60cfba54c5d69bd16477032cf8853056bfd447a1b96add6b270173c437`). The canonical52-cut carrier is extended by 25 source items, including actual verifier `mark`, actual approved Prepared body and helper, and exact accumulator/query-geometry carriers. `source-binding-audit.json` verifies every retained item and explicitly lists all function-boundary patterns. View.parse, verify_observed, allocation, math, query and checkpoint remain named source boundaries; no opaque global or stub has been accepted as a theorem.

| Exact target | Exit | Wall s | RSS KiB | Swap |
|---|---:|---:|---:|---:|
| tx1 Charon staging preflight a | 101 | 0.401 | 197184 | 0 |
| actual tx1 Charon b | 0 | 0.403 | 210308 | 0 |
| same valid LLBC, accepted static Aeneas b | 2 | 0.603 | 79200 | 0 |

Preflight a inserted staging declarations inside an impl and missed two imports; corrected staging declarations passed b. No production body was changed. The valid LLBC SHA256 is `2e4c8eff666427a14307c29d7d5884fa7fbe2d41f4361789dc7148f7855acd6c`; `has_errors=false` is checked before Aeneas. Aeneas rejects the actual `while a.next<k` loop at kit lines906:4–908:1, `InterpMatchCtxs.ml:2739` (`equal_abs`) during loop fixed-point matching. There is no emitted Lean result. `#print axioms` is inapplicable; no formal result is claimed.

Each job used a separate MemoryHigh6GiB/MemoryMax8GiB/MemorySwapMax0 scope, safe aggregate reservation≤16GiB below55GiB. Pinned Charon `daad69bea1114042a2d2fbd3dfde99922b152d4f57023bf8edb83e5a6f336af8`, driver `efdbe5b86c9f5f70c93810af08f358d4ecbaecf6f3e87517b1176689a8c28c45`, and accepted extended static Aeneas `4632746db1bf6c3953f2971078965a2a5a8ad6cf5f75636b46b397bc50c550b5` were reused without a rebuild/fork. Each receipt records revision, source/tool/command hashes, wall/RSS/swap and cgroup limits/events. Prior accepted static provenance is in `../public-binding-followup-20261016/extended-tool-audit.json` or its frozen archive.

`verify.py` verifies141 archive members, all3 receipts, source pins and valid actual LLBC. For the re-pin inventory's additional cone, archive paths are `actual-tx1/VerifyPreparedPrefix.llbc`, `actual-tx1/input/source-pins.json`, and `actual-tx1/input/lib.rs`. Exact failed-input snapshots are retained under `actual-tx1/runs`.

## Concrete pending source decision

`../../tools/tx1-caller-extraction-kit/proposal-tail/proposal.patch` is review-only and **has not been applied, compiled or probed**. It moves the three complete unchanged tail statements (geometry, while, checkpoint+mark+Ok) into `tx1_finish`. Original tail SHA256 `667270fc6fb4d18d0326bd0cc826759e7b980f2593ad8eabc9c93ffd12a1d8e7`; helper `9d3eec7ed6918a35bb6639916860037c5f466d7436919eb8a20d389b66a08a5c`; patch `ae3bb243df53c7f8cb75e1c49b5b2bfccea5deb447889dfc89b369a56096d980`.

The helper accepts owned `View`, `Box<Prepared>`, mutable owned `Accumulator`, `[E;29]`, unchanged public/proof borrows, k, H and Observer. All moved tail text remains byte-identical, including `&v,&p,&mut a,&g`. H is `Digest32:Copy`; sem stays in the outer function and no preceding borrowed argument escapes in the nominal Verified/Prepared result types. Moving View changes its drop point relative to outer sem; View consists of copy values/shared references and has no Drop implementation, so no destructor or allocation effect is introduced. Geometry Vec, accumulator Vec, Prepared Box and sem Box preserve their observable deallocation order. The ownership/evaluation/drop analysis and exact signature are in `proposal-tail/audit.json`; this is source analysis, not a successful Rust or extractor result.

The intended new real boundary allows a future explicit query/checkpoint continuation while retaining actual tx1 prefix control flow. It does not refine that continuation, close the existing verify_observed loop blocker, prove complete25 transcript-byte identity, or supply `semChalsZ_read.hread`. These remain open; custody is separate. No dependent rewrite probe runs before the lead/user's source decision.
