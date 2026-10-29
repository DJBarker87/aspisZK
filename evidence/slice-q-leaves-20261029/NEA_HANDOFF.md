# NEA slice-Q handoff

Branch: codex/cx-slice-q-leaves-20261029. Work is committed; no push. This is an incomplete slice: **3/20 local CLOSED-CONDITIONAL leaves, 17 OPEN; 0 composed rows closed**. The authoritative ledger is unchanged. No deployed security/release conclusion is claimed.

## Consume these local packets

| Function | PacketDomain | Main accepted theorem | Native / matched control |
|---|---|---|---|
| FibreIndex::new | Native constructor: all usize, including exact rejection. Successful model-carrier association: u.val<262144. | NEA_Index.all_inputs / accepted / canonical_index / fibre_caller / aligned_domain, L005 | K040/K041; alignment K005/K006. Result-shape triad: K042/K043, K046/K047, K050/K051; core copy K048/K049. K045 is excluded (compile error). |
| fast_domain::fibre_point | u.val<262144; table canonicality is derived, not assumed from callers. | NEA_PointComplete.cohort / emitted_interpretation (L051), NEA_PointBridge.selected/reads (L015), NEA_FieldProduct.emitted_cm (L006), NEA_TableCanonical.readA/readB (L050) | K017/K018; copy K012/K013. K024–K027 additionally check the later record-log/projection representation. |
| fast_domain::line_node | u.val<262144 only; no nonzero/distinctness/range-length/field-canonicality input premise. | NEA_LineComplete.cohort (L059), NEA_LineTail.reference (L058), NEA_LinePrimitive.double_value/sub_one_value (L060) | K029/K030; same NEA_line_opaque copy K031/K032. Timed verified-summary forms are excluded. |

NEA_CLOSED.json contains exact claims, domains, theorem names, receipts, controls and limitations. Native constructor case predicates express the reference through the payload/error interpretation; the successful cohort constructor is a Usize alias. K005 is an exact-expression scalar gate, not execution of for_range. All packets retain their named physical interpretation, lower CLOSED callee transport and P6/D188 tool/ABI/library/source/runtime qualifications. This is owner amendment fifth reclassification, never premise removal. NEB must prove each real caller's domain and same input/carrier/Result/effect bindings. Do not infer a composed row from these labels.

Relevant commits: 71248d4a58 (index), e0ba8673af and 4be8282ba4 (point/canonical outputs), 1e42726180 (line), 47066e5f13 (Result audit resolves the temporary hold in 4936fadbe8). Later commits preserve continuation evidence and corrections.

## What remains

NEA_SLICE_BRIDGES.md and NEA_STOP_AUDIT.json enumerate every one of the 20 functions with its exact obstacle. Key next steps:

- Both folds: accepted E005/L064 reference-to-cohort equalities and L066/L067 product laws exist. Full native gates time out; K034/K036/K039/K056/K057/K058 are excluded. Use small prelude/Horner cuts and explicit composition; E018 supplies reference candidates. Do not repeat a whole-fold timeout unchanged. Product-log and linear-callee controls are scaffolding only.
- Prefix and geometry: prove the actual arbitrary-prestate append/read/product/index window with a KMX disjoint-frame composition, then feed the existing NCB_PrefixNativeStep/CutTrace induction. K037/K038 timed out. Geometry also needs gather/backward/regrouping/allocator/nonzero/source-loop bindings. E008's generated external axioms are rejected.
- Dots/raw weights: inline raw field products require the exact emitted arithmetic and symbolic overflow/grouping/frame laws, never multiplication in Kani or an invented product/copy stub. Aeneas rejects E009/E010/E011/E017/E020 reference shapes; minimize and split their borrowed state. Full and partial reference candidates are UNVALIDATED, not bridge credit.
- Correction: accumulate_batched_with_node is **not** an Observer quarantine. Under deployed features prover is absent and trace::value is a no-op. Its blockers are row/push and basis/weight iteration/state/frame composition. Query_values/query_loop/mark do reach Observer=Option<fn> and remain quarantined.
- CM inverse/backend and QM inverse/try remain pointer-dependent; QM try also needs CM31::square outside Q. Do not clear quarantine by extraction, a literal callback, or a rename. QM neg's K001/K002 array-value fragment lacks the exact adopted enclosing-carrier association. NEA_TypeResolution.md is source evidence, not a formal pruning certificate.

## Budget, evidence and standard axioms

All authorized slots used: **80 native slots (79 cargo-kani invocations, one bounded GOTO inspection), 80 Lean runs, 20 extraction runs**. Codegen-only invocations, compiler errors and timeouts are never passes. No extra run is authorized by this handoff.

NEA_ATTEMPTS.jsonl / NEA_RESULTS.json record target, command, exit, wall time, peak RSS, swaps, source revision/hash and axiom output. Every admitted scope has MemoryHigh=6G, MemoryMax=8G, MemorySwapMax=0, TasksMax=64; Lean uses -M7000 and -j1. All swaps are zero. Every native invocation has the exact frozen graph, complete resolved features, offline mode, original KMX hash and unchanged frozen lock. No field multiplication was proved in Kani. NCO extraction pins, reference patches and exact failed/successful snapshots are retained.

NEA_AXIOMS.json accepts only exit-0 modules with a subset of propext, Classical.choice, Quot.sound (or no axioms). Error-recovery sorryAx/self-axiom output is excluded. The corrected WideLinear draft was not compiled after L080; it is not a replacement for the existing CLOSED NBG lower laws. State-erasure drafts likewise receive no credit.

## Ledger validation and adoption

NEA_LEDGER_DELTA.json proposes the three local packets and **no canonical row mutation or composed promotion**. NEA_NDT_LEDGER.json is a byte-identical authoritative ledger copy. NEA_validate.py passes own evidence checks and the unchanged NDT_validate.validate_invariants check on that copy. The full unchanged command

    python3 evidence/native-ledger3-20261029/NDT_validate.py --ledger evidence/slice-q-leaves-20261029/NEA_NDT_LEDGER.json

exits 1: `merged report corpus changed; refresh evidence snapshot explicitly`. NEA_NDT_VALIDATION.stderr preserves the rejection. The full delta is **unadopted**, not advertised as NDT-passing. The lead must explicitly refresh the evidence snapshot; no canonical validator or row was edited or bypassed.

## Cache, source and artifacts

Own host workspace: /home/dombarker/project-offloads/codex-cx-slice-q-leaves-20261029. Own cache: /home/dombarker/project-offloads/codex-cx-slice-q-leaves-cache-20261029. Imported read-only cache hashes and Aeneas library pins are in NEA_SOURCE.json. Accepted object/sidecar exports are retained under that cache's NEA_exports_20261029; exact paths/hashes are in NEA_HOST_FINISH.json. No cache was deleted. Only own rebuildable cargo targets, solver TMPDIR and exported object scratch were removed after all scopes terminated. No key/account/wallet operation occurred; no key markers were removed.

Research crates/ and programs/ are byte-identical to frozen 4bb3b3f51e16b4525f1d10336e2b0bcbbd775387. Only own evidence and NEA modules were committed; harness edits exist only as scratch patches. No ELF rebuild was triggered. The default f8c0ec72621fd5029a97d796c4a3623d0dc44a8e7074122372f9872915d143d4, devnet 63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299 and Pool 121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548 hashes are inherited, not rebuilt/reproduced here.

Headline AspisR1.RPx_Deployed.deployed, frozen3, the L154 statement parameter, narrowed D188, RuntimePersistence, privacy, the two-transaction design and the 100-bit PER-ATTEMPT target remain unchanged. No XRn join kit or stand-in was used. No full release replay or unchanged regression was run.
