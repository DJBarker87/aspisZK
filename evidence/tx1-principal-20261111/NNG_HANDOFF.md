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

## Interface corrections after LIB carrier delivery

NNG-F1_ENV_CALLS.md: the provisional fixed-Calls target could not express Env.reservation changing between environments. L156–158 validate Env-dependent calls and pointwise source-call/field graph equality at the SAME Env. The old all-Env fixed-call equalities are valid conditional facts but are not intended installation interfaces.

NNG-F2_CARRIER_DOMAIN.md: actual LIB_VScalarCarriers.QM31 is a canonical subtype, so global raw-Q injectivity in the provisional Representation is too strong. LIB_VCarriers.Prefix also retains caller parser provenance. The CURRENT interface is NNG_DProjection136 (L171), DProjectionLaws (L172), DEnvObserved136.Target (L173) and DOccurrenceLaws136 (L174). It keeps the ORIGINAL semantic a.prefix_ and uses qDom-local injectivity. Only returned raw scalar canonicality for running and masked is needed at the terminal guard, derived internally from CLOSED134 and reached add; these are not new finishInputDom clauses. No VLib field is constructed by NNG.

Canonical suffixes NNG_Canonical136.body_ref compile at L163 and equal the frozen Ref after inserting pure binds for lexical alignment. SourceStep136 (L154) and LawStep136 (L166) prove forward single-source bind/trace restriction and complete stopped-prefix rules. The earlier source root/payload/circle-guard proofs (L167/L169/L170) validate the suffix proof pattern but retain the superseded strong Representation; they are not for candidate use. NNG_DSourceRoot/Payload/CircleGuard independently revalidate that pattern against the corrected carrier interface (queue DSOURCE, attempts L175 onward).

NNG_FromFnValues136.first/second (L151) give the exact two raw source arrays, with callback laws only at visited indices. Current direct emitted occurrence adapters are NNG_EnvOccurrences136 (L158); they accept the DProjection decoders without change. NNG_Model134.call_model remains the correct rounds source-model transport.

## Domain-aware source fold checkpoint

Actual recorded use now: 144 Lean scopes, 1 extraction, 1 seed scope, 0 Kani (waits separate). Highest submitted id L183; budget is counted by launches, not numeric gaps. No timeout, memory kill, cap increase or unchanged failed-shape replay.

L175 generic DLawStep; L176 DSourceRoot (both copy/unwrap arms and all output fields); L177 DSourcePayload; L178 DSourceCircleGuard; L179 DSourceMark5; L180 DSourceCircle1; L181 DSourceBeforeZ1; L182 DSourceRecord26; L183 DSourceCircle0 all pass with standard axioms. Each theorem is about actual NNG_TreeSuffixes code against the canonical suffix. The repeated row26 getter is internally supplied by pure_value at its first source occurrence, then reused without adding an event.

The current remaining fold starts at state_before_z0 (f_state_before_z0), carrying the locally saved row25 equality; then mark4/terminal guard, arithmetic/index steps, decode87/record25/mask/std arrays/mapPublic/terminal/claims/mark2/rounds. Carry qDom running from CLOSED134's returned arm and qDom masked from the actual final add into the scalar guard; neither is a caller clause. Root generic theorem must state RowSpec_136 on DEnvObserved.producer; then instantiate all entered-call clauses from LIB's VL⋆ and CLOSED source models. Still no 136 candidate or row credit.

## Complete domain-aware source fold

L184–L186 compile state/mark4/scalar guard; L188–L194 compile final additions/multiply/decode87/record25/mask; L195–L196 and L204–L206 compile native indexing/from_fn arrays/mark3; L203 and L207–L209 compile full mapPublic/terminal/claims/mark2; L212 rounds and L213 NNG_DRowSpec136.fold complete the literal rev3 RowSpec fold. Every returned/error/abort/diverge arm and its actual event prefix is retained. qDom running is derived at the actual rounds return and qDom masked at the final addition; saved getter equalities are internal facts. No new caller clause or library instance.

All passing axioms are standard. Failed L187 (placeholder), L197 (dependent rewrite), L200 (own edit indentation), L210/L211 (field argument order) are excluded. No timeout or memory kill. Queue path typo was a prelaunch own-input error and fixed without a scope. L198/L199/L201/L202 were never launched.

NNG_DRowSpec136.fold is complete conditional support, NOT a candidate: closedOccurrences must still be discharged with LIB VL⋆ and each CLOSED deterministic model. The entire generic source fold is now green; no source body remains unassociated. Remaining work is concrete input/carrier/Calls/effect installation and reached-domain proofs from the LIB modules14–18 exports. Latest reviewed LIB commit bdbeea224fd delivers circle/terminal; rounds graph and VL⋆ are not yet delivered. Parent candidates remain child-first. Own-root raw ax2 and combined import are next validation tasks while LIB finishes its bundle.

Focused combined NMQ + DRowSpec136 + deterministic Model134 import passes L214 (21.056s,6438468KiB,swap0). Raw ax2 L217 fixtures plus L218–L231 audits53 current fold/model/occurrence roots in14 small groups: all raw/collect axiom sets equal, all standard-only. NNG_FOLD_AUDIT_SUMMARY.json records results and compressed raw reachable/edge witnesses. No source/candidate claim follows from the audit. Driver semantics are unchanged from NMP except own manifest prefix (diff retained), O3 link L216. Current next work: committed LIB carrier objects seed L232, scalar/array transport and deterministic circle/decode raw call adapters. LIB bundle still undelivered at reviewed bdbeea224fd.

## Concrete carrier and domain progress

LIB committed revision bdbeea224fd is copied/hash-checked into NNG_LIB_objects (L232/L251), sources retained under NNG_LIB_inputs with exact provenance requests/pins. Read-only fallback paths from its accepted L143 receipt are appended behind NNG_RSL3 and own objects to resolve unchanged NMS support (L233 missing-import failure excluded). L238 lacked the projection's local classical Decidable instance; L239 corrects it and passes. L240 namespace/literal-index elaboration failure is excluded; L245 corrects it and passes. Unlaunched queue ids L234–L237/L241–L244 have no budget credit or result.

L239 NNG_LIBScalar: total canonical projection with an input canonical fallback; inverse on Domain and injection on Domain only. L245 LIBArrays: array/claims/challenges roundtrips, eta and at28. L246 LIBArrayDomain: canonical lowered arrays, raw-domain inverse and get-domain. L250 LIBData: original Prefix/Public lowering, point injectivity, c1Root/state/bytes and fixed32 root fields. No VLib field instance or child definition in any NNG module.

L247 ModelCircle and L248 ModelDecode preserve full raw source-model Results; L249 TypedEvents proves exact typed site argument selection for effect decoding. L252 LIBRoundsCanonical derives running and alpha canonicality from the actual returned deterministic CLOSED134 source model (never the native-cut image). L253/L254 compile arithmetic transport and LIBField exact add/mul plus returned canonicality from LIB's canonical arithmetic. L255 revalidates existing InstallClaims source transport; L256 ModelMask transports full FIp mask Result. All passing #print axioms are standard; none is row credit. L257 rebuilds rev3 RSL_Pool privately before any LIB_Env-dependent import. Next NNG_LIBClaims source graph covers both reservation arms, then concrete getter/decoder/effect associations. LIB rounds graph and VL⋆ remain undelivered in the reviewed branch; a text query is pending while independent proofs continue.

## Concrete 136 call models

L257 rev3 RSL_Pool replay passes before LIB_Env consumers. L259 NNG_LIBClaims full actual source call projects exactly to LIB_VClaims.eval at the same Prefix and Env, covering both reservation outcomes; L258's elaboration errors are excluded. L263 NNG_LIBRecords getter/payload and scalar-array raising pass after splitting failed combined decoder shape L260/L262; L264 isolated LIBDecode passes with exact native offsets/frame. L265 Digest transports identical partitions and runtime reply (no SHA unfolding); L266 ModelTerminal preserves complete error payloads via an explicit bijection, not a collapsed fabricated error.

L269 LIBTerminal proves native argument identity and the full result projection to LIB_VTerminal.model, including abort/diverge and canonical returned scalar. L272 MaskCells and L277/L278 symbolic low/high source-array projections pass; L279 LIBMask identifies the SAME 16+10+1 arguments with the CLOSED mask model. L280 typed digest effects and L281 LIBCircle preserve complete source values and exact child event logs. L267 was replaced by an isolated generic dependent lift lemma; L270 was an ambiguous get name; L273 literal-bound inference repaired explicitly. No timed-out/killed run or cap change.

LIB delivered standalone fields/graphs through565aec6e7ef; sources and exact objects copied/hash-verified in L282 (36-module dependency closure). No concrete value VL⋆ : RSL.VLib is present in that delivery. NNG has not constructed a VLib instance. A text query identifies this exact missing library-owned value while proof work continues. L283 RoundProjection isolates canonical lifts; L293 LIBRounds full model projection passes after retiring unrestricted dependent rewrites (L284/L286) and explicitly supplying CLOSED returned canonicality (L289 excluded). L294 RecordReached and L295 RecordFrame prove decoder/circle domains and payload2 length from SAME actual getter/payload returns, as internal facts only. L296 ConcreteCalls136 supplies one complete raw dictionary, and L297 ConcreteInput136 is queued: neither is a VLib field instance. Next: fully instantiated equalities to LIB child fields, then the remaining trace-wide reached-value association; literal candidate still awaits LIB-owned VL⋆. Parent candidates remain child-first.
