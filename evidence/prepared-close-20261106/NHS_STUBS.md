# Native cuts and callee laws

No new field multiplication stub, function contract or stub_verified use. No writable static, Option<fn> or function-pointer-dependent assertion. New pending harnesses use local owned Vecs/records and no callee stubs beyond the exact KMX copy mitigations. KMX patch SHA256 bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67; KMX_stubs.rs ad8efb63d8ff791274c91eff9ccc5b9fb126f5a3ac7f27aa811ca11b8e25c138. No private copy implementation is introduced.

| Cut | Paired semantic law | Domain / SAME-value connection |
|---|---|---|
| NGN S0 | NHL_OpeningPacket.seed/newStart; retained NFW seed/state certificates | Original sem.transcript/hash, fixed seed29/tag1/state32 carriers; existing digest=H interpretation |
| NGN S1 gamma | NGT_CallerInterface.scalar; NHL_PreparedScalars.gamma | row27,y1=928,true; NHS_CallerWidths.reached/scalar_bounds; SAME NGT block and reduction |
| NGN S2 kappa | NGT_CallerInterface.scalar; NHL_PreparedScalars.kappa; original serializer sourceBytes | row28,exact32-byte array,false; original inactive from sourceView; SAME serialization and prior transcript |
| NGN S3 alpha0 | NGT_CallerInterface.scalar; NHL_PreparedScalars.alpha0 | row29,round0=224,false; same block/reduction |
| NFW S4 alpha1 | NHL_PreparedOpening.double; NGT_CallerInterface.scalar | row30,false; NHS_FoldDomain.length derives payload256 from actual extensions and round1=224 |
| NGN S5 queries | NHS_QueryPacket.source/domain; NHK_Invocation.producer and NGQ_TRANSCRIPT.actual_queries | row30/31 from SAME fold; SAME v.final_message=2048; full Result/state AND chronological attempted events retained |
| NGN S6 rho | NGT_CallerInterface.scalar_k; NHL_PreparedScalars.rho | row31/32,empty; SAME post-query transcript, sampled rho and final advanced state |
| NGN S7 powers assignment | NFW_PowersCohort.source; NHS_PreparedPacket.source | SAME gamma canonicality derived upstream; exactly29 outputs; entire assigned scratch transported |
| NFW/NGY S8 prepared_claim | NHL_PreparedClaim.claim; NGU_PreparedClaim.packet / NGY_Thread | SAME successful semantic finish, compact464 check, same928-byte expansion, canonical inactive/gamma/kappa and SAME powers |
| NGN S9 record/Box | NFW_PreparedFields.source; NGN_TypeTransport; NGN_K029/030/031 | SAME eleven pre-return fields; allocation identity and value-corruption/different-allocation controls |
| NHS pending one iteration | NHS_PendingStep.source; retained Port3_NativePendingStep.step | raw64 arbitrary prestate, one current weight, arbitrary index/window; TX1 input weights are zero64 from SAME accumulator initialization. Native test sets other weights zero; no general TX2/nonzero-vector credit |
| NHS pending allocation/record | NHS_PendingReservation.source_eq; Port3_NativePendingBody.extracted; Port3_NativePendingInstall.emitted_exact | Local actual filled reply, both Results, SAME raw allocation, final terms0; no successful allocation is assumed |

NGN returning stubs overapproximate CLOSED callees. QLog.reply is Rust Result<[u32;22],Error>, with transcript.after separately logged. NHS_QueryPacket projects NHK's outer returning Result to precisely that pair. Error/fail/div consumers are checked separately; attempted events never disappear. No mismatch requiring a predecessor edit was found.

Inherited powers/claim products keep their original Lean-discharged field laws and canonical domains (LPh/NFW/NGY tables); they are not re-proved or run natively here. Trust is the approved P6/D188 option-A semantic-transport reclassification, with existing runtime/compiler/ABI/std/allocator/Aeneas/source-to-ELF assumptions retained.
