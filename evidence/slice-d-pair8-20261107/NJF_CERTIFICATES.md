# NJF reviewed hybrid certificates

**TX2:129 pair and TX2:115 finish: two local gate-checked closure candidates. Zero authoritative ledger promotions; credit waits for the next ledger gate. Target not yet established.**

## Native parent cut

`NJF_SliceCuts.cut` (L024), `NJF_SliceCuts.evaluator` and `NJF_CutEvaluation.evaluated` (L025) transcribe the returning Rust Result, exact argument windows, full scratch/Parts post and chronological prefix of frozen weights.rs:279–288. `NJF_RegularCut.G` extends entered outer fail/div prefixes under (an); it does not fabricate Rust Err arms for abort-only callees. All eight actual verifier Error constructors are explicit.

The oracle's exact permitted writes are scratch[0..64] and Parts[0..7] for regular, Parts[0..7] for high, plus its LOCAL log. This conservatively overapproximates the real CLOSED frame; the real untouched cells are restored by substituting the child's full Result and proved frame. It adds no stronger caller restriction. w/alpha/f/ap0/ap1 remain immutable. No writable static, Option<fn> property, contract, stub_verified, native field product or new runtime trust row is used.

| Window | Passing / matched failing control |
|---|---|
| args | NJF_K012 / NJF_K038 |
| control | NJF_K014 / NJF_K015 |
| scratch | NJF_K006 / NJF_K007 |
| parts | NJF_K008 / NJF_K009 |
| common/partial | NJF_K042 / NJF_K043 |
| high args | NJF_K018 / NJF_K040 |
| high value | NJF_K022 / NJF_K023 |
| high pre 3..6 | NJF_K030 / NJF_K031 |
| high pre 0 | NJF_K032 / NJF_K033 |
| high pre 1 | NJF_K034 / NJF_K035 |
| high pre 2 | NJF_K036 / NJF_K037 |

All controls above fail the intended assertion, not compilation, a timeout or an unrelated pointer/count assertion. In particular K038 and K040 fail copied ap0 words; K043 fails the direct projection of the copied common word. K013/K017/K019 are historical pointer-oriented failures and are NOT copy-specific credit. K039/K041 timed out and are excluded.

All sources/configurations are in SOURCE_INDEX.json and content-addressed .xz inputs. The parent and five oracle function bodies are identical across admitted windows. Only oracle setup representations, observation-selector partitions and control-only assertions differ. The K006/K008 array-backed reply/pre-state represents every decoded length64 borrowed-slice value; NJF_ScratchCarrier.covers/injective (L039) proves that no Vec payload is excluded. The native boundary ABI itself is &mut[K], not a Vec replacement. K024/K025's redundant Vec-setup variant timed out and earns no credit. Parts K026 passed but K027 timed out; the packet uses K008/K009.

K030/K031 cover arbitrary slots3..6. K032/033, K034/035 and K036/037 cover literal observation slots0/1/2; NJF_LowSlots.complete/parts (L042) and NJF_WindowPartitions (L036) reconstruct the entire seven-cell snapshot. Selectors affect only observations, never parent execution or child values. Every copied field uses exact KMX patch bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67. NJF_CopyFrames (L030), over the canonical KMX_CopyMeaning value laws, proves disjoint scratch/Parts windows and the outside frame. Physical validity/nonaliasing retains the existing Rust/P6 domain, not a new assumption.

## Forward (y)(3) substitution and call structure

| Segment | Kernel/source certificate and caller domain |
|---|---|
| Initial/powers4 | NJF_PairInstantiation.source (L018), NIW_AlignPowersReply.source: SAME two alpha values; canonical replies derived internally |
| Allocation/zero64/zero7/guard | NIQ_K002/003,005/006; NIG_K111/112; NIT_ControlCuts.guard; NJF_AllocatorInstantiation.source (L016): actual reservation/allocation arms, zero64 invariant, real guard Bool |
| Regular/shared | NJF_RegularInstantiation.source (L007), SharedContinuation.source (L009), RegularContinuation.source (L015): actual complete child Results at decoded arguments, Err writes, no suffix; post/frame/domain from NIG_PairFrames and NIW source helpers |
| Common16 | NIG_K009–016; NIW_AlignCommonExecution.observed/TraceLog.collected/PostLog.source: one native step, actual multiplication reply, finite Lean induction, full owner/cell frame |
| Partials/high | Corrected NJF windows above; NHM/NHX CLOSED child laws, NIG_PairFrames.high, NIW_AlignPartialPhase.trace: actual common/partials, SAME w/ap0/ap1 and post-regular Parts |
| Low16 | NIG_K019–030; NIW_AlignLowExecution.observed/TraceLog.collected/PostLog.source; natural multiplication/scale clauses discharged, full cell frame and induction |
| Group/factored | NIT_K003/004; NIW_AlignGroupPhase/TailPhase.source, NHX group/factored packets: SAME low16 and by-value extra; only parts0 changed by group |
| Libra4 | NIG_K096–107; NIW_AlignLibraExecution/TraceLog/PostLog: actual field/read/multiply/add Results, full parts4 frame, entered abort prefix, finite induction |
| Powers7/final7 | NIQ_K007/008; NIG_K031–042; NIW_AlignFinalExecution/TraceLog/PostLog: SAME kappa, zero sum, actual arithmetic replies and seven-step chain |
| Whole pair | NJF_PairInstantiation.source/root (L018): all preceding segments chain to the SAME emitted pair. Its primitive Domain is an internal helper input, discharged at actual NEW in the deployed root |
| NEW/PairPort | NIG_K115/116,117/118; NIW_K006/008 factors and009/010 rest; NIW_AlignOwner.returned and source PairInstalled/FinishPairCertificate: SAME owned pre-call payload, all raw fields, no address-implies-payload inference |
| Finish | NIG_K119/120; NJF_FinishInstantiation.source/root (L020), FinishObserved.source/source_log (L021), NJF_Root.finish (L022): SAME round0/round1/NEW/pair/dot arguments, full Result and complete chronological source list, first error/abort and no suffix |

These are native universal-oracle cuts specialized FORWARD with CLOSED child results, then equated to the source invocation. No inverse raw-log projection is required or assumed. Old PairEdges' narrow regular_post and NIW's Vec-replacement boundary are not whole-state native credit here. Existing unchanged loop/NEW/finish cuts are reused with their admitted source/receipt pins, not rerun.

## Admission and trust

L043 combined import includes NGK_COMBINED_IMPORT, NIU_COMBINED_IMPORT, NIW_COMBINED_IMPORT, every new semantic module and RPx_Deployed.deployed. L044 raw ax2 audits224 roots, standard axioms only; NFX scan exits0 on15195 modules with zero dangling references, incompatible owners or import mismatches. L037 reproduces eight fixture identities in the SAME proof binary. Exactly two complete changed-closure audits ran (L041 historical; L044 final).

The deployed pair/finish positive root is NJF_Root.finish; its inputs are data, retained SAME-call NIG_FinishInput.Domain and the reviewed PairPort cut. NJF_PairInstantiation.root is an internal primitive-domain helper, never a standalone deployed-row premise. NJF_HYPOTHESIS_AUDIT.md and NJF_STATEMENTS.json give the exact distinction. Every child Result clause/domain is discharged internally at the SAME entered arguments.

Every typed cut/native association is reviewed P6/D188 option-A semantic transport RECLASSIFICATION, not removal. No trust item added/removed; RuntimeCpiReadonlyEntry7 remains PENDING/unused. The final gate is focused coherent cached validation, not a cold release replay or ELF reproduction. Global 100-bit PER-ATTEMPT soundness, privacy and the two-transaction design remain unchanged and not yet established.
