# Complete hypothesis inventory

`NHZ_DRIVER.events_from_cuts` and `NHZ_EXPERIMENT.same_law` are PROVED-conditional model theorems. The deployed plan instances remain OPEN. Definitions/records are expanded below; neither generic theorem discharges existence of its physical inputs. No new axiom or trusted runtime row is introduced.

## DRIVER.events_from_cuts

| Binder | Source / classification | Exact responsibility |
|---|---|---|
| A | statement type parameter | Full terminal value, including Rust Result and mutable-state carrier where applicable. |
| hashv | statement parameter | Real partial digest function, not totalized. |
| tx1 | statement parameter; OPEN native driver owner | Must be the actual installed TX1 effect syntax. The theorem deliberately does not label an arbitrary code argument as a frozen native body. |
| cutCode | statement parameter | Source-order tree of reached per-callee effect syntax. |
| observed | statement parameter; OPEN native producer | SAME invocation full Result and chronological attempted log, including unsuccessful syscall. |
| cuts | CLOSED generic composition + OPEN physical installation | Inductive leaf is NGQ_Cuts.Trace, NOT an arbitrary Result equality. next threads the returned value (including full pre/poststate); fail/div have no tail. Physical existence is still needed. |
| ordering | OPEN native ordering result, TX1/prepare/verify_observed owners | Literal `cutCode = tx1`. Not proved by collecting local packets. It must include every pure guard, semantic verifier, batch/replay, query-loop and writer call in source order, with state/frame installation. |

The imported CLOSED leaves do not justify an unconstrained `cuts`: NHK_Invocation.producer supplies queries_cut only at the SAME transcript/row/payload; NHZ_scalar_block_cut supplies the three NGT successful Block reads only (NGT's Block requires three ok edges); NHZ checkpoint lemmas supply the actual NGC sourceProgram's three reads and every fail/div prefix, on its SAME WriterDomain. NHS_QueryFailures retains query-level Error/fail/div, but is a constructor Result theorem, not a complete constructor digest trace. NFS_LoopTraceDefs uses **NFP callee events**, not SdkC_Source.Query: opening/dots/arithmetic/geometry/accumulate events require their own source effect interpretation. It must not be cast as a digest log.

Exact retained NHW op9 equation (read from immutable HEAD, snapshot committed):

```
∀ v, NHL_PrepareModel.Reaches (nativeChildren base) reserved D proof v →
  base.op9 D pub v.semantic hash none =
  (RowShape_InstalledSlots.verifierOps base B std).op9 D pub v.semantic hash none
```

NHW_DriverInstantiation.source has the same equation on its explicit packetOps dictionary; full statement is in NHZ_READONLY_NHW_DriverInstantiation.lean.txt. Even its discharge would supply a Result equation, not the missing complete parent event association. No known chronological exporter for the entire TX1 wrapper is assumed. Digest/error slots are op43/op44 in the adopted SInt2 cohort.

`prefix_from_cuts` adds sha256/H (parameters), P1 (accepted successful-return SHA256=H realization), and RuntimeSyscall (accepted successful-return forwarding). It invokes NGP_OracleTransport.prefix_of_native. It does not assume totality or infer exact reply equality on fail/div. `frame` adds arbitrary earlier log `before`; this is a log append law, not a native heap-frame certificate.

## EXPERIMENT.same_law

| Binder | Source / classification | Exact responsibility |
|---|---|---|
| W,A,C,Tx | statement parameters | SDK/allocator/error/bank transaction types. |
| L,copy,allocator | statement parameters; laws retained transitively | Actual SDK library, copy operation and allocator dictionary; existence alone supplies no caller facts. |
| c,err,r | statement parameters; OPEN deployment instantiation | SAME installed configuration/error/reservation Result. No allocation success assumed. |
| native1,native2,hashv | statement parameters | SAME native wrappers and partial syscall. |
| a | game adversary parameter | Arbitrary adaptive SCE_Experiment.Adversary; SAME first phase and saved/post/final-selected second phase throughout. |
| extraction | OPEN native result, driver/extraction owners | Exact S2W_DigestExtraction.AeneasExtraction for DrvC_Installation.sdk cfg and these native functions. Retains the pre-existing whole-source interpretation. P6/D188 tool trust is not evidence of its instance. |
| std | accepted TrustedStd law | Exact copy semantics on caller-proved valid references. |
| D,words | statement parameters | Original LiteralByteProtocol.Decoder and CanonicalCutEnrichedTranscript.Words, unchanged. |
| owners | OPEN installation packet / canonical global-owner laws | Exact FIp_GlobalOwners.Owners cfg and matching Rc2 boundaries, same as ARX_Mass/Residual; not derived from code import. |
| Q0,Q1 | L154 statement parameters | Q=Q0+Q1. |
| queries | L154 parameter | Universal literal ARW_Induced.issued length bound. Counts duplicate occurrences and both reached adversary phases; no fresh/distinct-query substitution. |
| physical | statement parameter; OPEN physical observer | Admitted physical experiment Program, with SAME stored/public/fail observables. Raw unaudited deployment is not identified with it by a name. |
| realizes | OPEN observation producer, experiment/native driver owners | ∀H, eval H physical = eval H (ARX_AdmittedRuntime.runtime … a). Full occurrence log and RunView, same admission/zero-extension. This is an exact sufficient interface; **not discharged here**, not an accepted runtime law. |

`NHZ_Realization.realizes_from_fields` derives `realizes` from five explicit producer fields, rather than assuming a probability inequality: (trace) outer occurrence-list identity; (admission) physical observer isSome iff Nonempty ARU_Support.At; (events) RunView's nested log identity; (carrier) SAME canonInput from submitted SAME source first outcome; (failEvent) literal SCE_Experiment.accepted flag. Its other parameters match the inventory above. All five physical fields remain OPEN. The theorem asserts no equality between unadmitted native abort behavior and an accepted run.

`support_from_events` retains `entry : ARS_Coverage.SupportedEntry` (a Type, returned as Nonempty support) plus firstObserved/secondObserved and their two NativeAssociations and two Agrees. `entry` expands to saved/post1/post2/final1/final2/w1/w2, admissions on response-selected entries (accepted RuntimeEntrypointAdmission), actual accepted1/accepted2 (approved-game antecedents, OPEN native producers), p/t/u/actions and game a–d (approved game fields), RuntimePersistence (accepted DATA ONLY law). The second syntax explicitly uses entry.saved/post1/final1; independent runs cannot be substituted. The two Agrees are query-restricted source realization, OPEN until associated observations plus successful-return laws prove them. They are not assumed uniform/fresh or independent.

`replay_support` retains extraction, actual entry/native/H, successful-return RuntimeSyscall and full ARS_AccountReplay.Consistent on ART_PartialAccount.account. ARW_AdmittedSupport.original derives support and exact replay without conditioning. `pointwise_from_events` uses exactly those supported event inputs, plus the same std/D/words/owners/Q0/Q1/queries as same_law; ARW_AdmittedBudget derives the work bound, ARX_Domination supplies the unchanged failureMass inequality.

## HISTORY, CARRIERS, trust, and what is not discharged

NGR_HISTORY.saved_to_loaded and NGS_CARRIERS.same_inputs_or_collision are imported/read-only and audited together. Their native writer/reader/getter/scanner/encoder/source-protection hypotheses are NOT inferred from NativeAssociation. They prove bytes on specified entries, not that an arbitrary physical observation is those entries. Their exact binder sources are NGR_HYPOTHESES.md and NGS_HYPOTHESES.md; both files are hashed in NHZ_INPUT_PINS.json. ARX_Join's admitted source instance already uses the history/carrier chain; this job does not claim to construct a new physical NGR/NGS instance. Importing them is not discharge.

The collision fork is the literal existing Hiq recorder event at Q+2965. NGS_COLLISION_DERIVATION.md accounts 1018+903+1040+4 once. same_law retains ARX_Mass's accountLoss=6*(Q+2965)^2/2^256 and ARX_Residual's total Q. No extra collision event, abort multiplier, event normalization, game change, privacy change, grinding credit or duplicate discount.

Accepted SDK/Std/allocator/ABI/compiler/Drop/Aeneas/source-to-ELF and narrowed P6/D188 transport remain as inventoried by NGK/NGP and the owner. RuntimePersistence, RuntimeReturnData(nonempty1..1024), RuntimeMemcmp, RuntimeClockSlotBinding and RuntimeReturnDataClear are retained, not discharged. This job adds none. Standard kernel axioms only are allowed; ax2 and scanner results are recorded separately. Target not yet established.
