# NNG TX1 principal handoff — active

Target not yet established. No candidate or row credit yet. Branch codex/cx-tx1-principal-20261107; no push.

Order: 136 → 137 → 087 → 094 → 328 → 345, then 344/333/330 by instantiation. Specs frozen at RSL revision 3 (lead amendment 2026-11-07). Stage 1 will freshly emit verify_finish and audit post-loop returns, then compose concrete CLOSED children at each occurrence. NMP fresh emissions are reusable for 137/087; NMT emissions for 094/328/345. LIB owns all concrete field instances (LIB0_MAP modules 14–18); do not construct a VLib instance in NNG. The 136 candidate will be this fold applied to LIB’s VL⋆.

Limits: 2 extraction, 400 Lean/link/audit scopes, 10 Kani only bc-flagged exits; one capped scope at a time, 6G/8G/no swap/64 tasks, Lean -M7000, no cap or timeout increases. Admission requires exit 0 and allowed:true, share<6, disk≥40GB. Use unchanged SInt2 launcher. No shipped-source, trust-row, key or artifact change authorized here.

Frozen crates/programs-r1/lock 4bb3b3f51e16b4525f1d10336e2b0bcbbd775387; Pool b936275465. Inherited ELF pins f8c0ec72…/63ad3e9c…/e0e49c34… are not new rebuild claims. Standard axioms only; audit own new roots only. Increased extraction reliance under bm is retained P6/D188 reclassification, not removal.

## Stage 1 emission

E001 freshly emitted actual frozen verify_finish with complete opaque boundaries: exit0,60.30653578s,536564KiB,swap0. Tool, source, feature, graph/lock and raw LLBC/output pins are in NNG_emitted/verify_finish and E001. bc audit PASS: no deployed loop; every error/panic arm retained. Generated equality trait compilation interface repair is in NNG_REPAIRS.md (L003 rejected; L004 changed shape passes). Types L002 and parameterized body L004 compile, the latter prints only standard axioms. These remain support, not a candidate or child installation. Ledger25 retained export copied/hash-verified in L001; all selected imports and Aeneas objects pinned per scope. No Kani, new trust, shipped source or ELF change.

## Library mapping review

Read mapping-only commit8c9ffd24f0d from branch codex/cx-lib-map-20261107 (that branch was subsequently removed/renamed by its owner; immutable commit retained). No concrete instance is delivered by that commit. NNG_LIBRARY_REVIEW.json pins the mapping and relevant F1/F5/F7/F8 flags. No frozen spec is changed. F1 (fallible reservation absent from Env) is a pending top/library issue; conditional RowSpec work remains possible but cannot silently fix reservation to success. Canonicality/domain support from NLU/NMC/NMO is reusable; no new parent condition is introduced. Pool payload parity independently checked: all20 carried Pool files match b936275465.

## Resumption after lead amendment

Inherited recorded use: 32 Lean scopes, 1 extraction, 1 seed scope; 0 Kani. Highest reserved local id L069; L030–031/L034–067 were not launched according to the committed ATTEMPTS log. Continue with L070. Prior modules are support only. The rounds native-cut image is not an admissible field model: use CLOSED134’s model conjunct. Failed equality support is not used.

Next module: NNG_Row136Fold, explicitly stating RSL.TX1_136.RowSpec_136 VL and folding source-order call occurrences against RSL.TX1_136.Ref. Each occurrence must identify its corresponding VLib field under the graph of its CLOSED deterministic model. No concrete VLib field installation belongs to this lane. Rebuild the RSL import closure privately from rev3 sources before loading it; no rev2 RSL objects are admissible.

## Rev3 conditional fold stage

L070/L071/L072 privately compile byte-identical rev3 RSL_Base/RSL_Verifier/RSL_TX1_136 in NNG_RSL3 before any RSL consumer. L075 compiles NNG_Row136Fold.fold: body VL calls = RSL.TX1_136.Ref VL a under FieldGraphs. Its Target explicitly names RowSpec_136 on the fresh emitted function. Standard axioms [propext, Quot.sound]. L073 had a structure-layout parse failure; L074 exposed a simplifier proof-shape failure; L075 replaces rewriting under dependent decisions by extensional equality of the call record. No timed-out or memory-killed run occurred.

This is conditional support only: FieldGraphs and the actual emitted-to-interpreted body association are uninstalled. It is not a candidate. Next: actual emitted Result plus typed trace observation, and model-graph occurrence equalities (no native-cut rounds model). No VLib field instance has been defined.

## Actual emitted observation stage

The 31 lexical suffix erasures now compile (L085/L086/L088/L090–092/L094–118). L119 NNG_TreeEmission.erase_tree composes them and proves erasure of the typed call tree equals the ACTUAL fresh emitted verify_finish for every complete Calls dictionary and original Parent. L120 NNG_Observed136.producer_tree ties the producer's value to that emission and events to its SAME typed trace. NNG_Observed136.Target states literal RSL.TX1_136.RowSpec_136 VL on this producer. The older Row136Fold.Target's arbitrary observation adapter is superseded by this precise target; neither is a proved row.

L080 compiles the occurrence-model graph adapters for semanticRounds, claims, terminalQm31, both circles, mask, both adds/multiply, record25/26 including reused positions, decode87/decode0 and payload2. They conclude equality to corresponding VL fields, conditional on the SAME deterministic model graph and source relation. No field instance is defined here. L122 fixes standard structural equality; L123 proves graph-bind and exact observation-prefix algebra. All passing theorem axioms are standard.

Retired proof shapes: whole-body erasure simplification L077/L078; generic simplifier matching through ControlFlow matchers L087/L093. They are replaced by explicit symbolic Result congruences at each branched suffix; no reply is fixed to Ok and no cap/timeout is raised. NNG_tree_fission.py then NNG_explicit_erasure.py reproduce the final suffix proofs. No row/candidate credit.

## Direct emitted occurrence / standard stage

L126 proves the complete source interpreter equals its deterministic observation graph; L128 projects it and proves membership for the ACTUAL emitted producer without an endpoint, log, successful-child or result hypothesis. L127 NNG_Model134.call_model transports to the deterministic model expression appearing on CLOSED134’s source side; its statement contains no native cut/image.

L129–131 prove the direct emitted-call-to-VLib-field graph adapters. Unlike the earlier model-only adapters, their statements explicitly contain actual `c.c10/c.c8/c.c7/c.c13/c.c11/c.c15/c.c12/c.c4/c.c5/c.c6` calls at typed source arguments. Their source equations, field graphs and entered domains remain to be installed from LIB plus caller proofs. No VLib field instance is defined here. NNG_LIB136_INTERFACE.md records the exact intended consumption and the still-owned raw-to-canonical fold gap.

L133 proves BOTH standard fixed32 copy/unwrap arms. L138/139 prove exact array selection and the first source closure; L147 proves a portable Usize lower bound, L149 its offset no-wrap consequence, L150 the exact second source closure. L148 proves domain-local from_fn loop composition: callback success is required only at actually visited indices (not the stronger inherited global-purity lemma). The failed concrete-size offset reduction at L143 is retired: Usize.size is intentionally opaque; no 64-bit numeral is assumed.
