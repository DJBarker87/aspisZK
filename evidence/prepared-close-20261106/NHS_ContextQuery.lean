import NHS_ContextDomains
set_option autoImplicit false
noncomputable section
namespace AspisR1.NHS_ContextQuery
open Aeneas Aeneas.Std Result AspisR1CurrentCaller
/-- Instantiates the CLOSED NFS consumer on the actual reached Context. The
remaining current-op7 dictionary/physical installation is reported separately. -/
theorem source {F C H : Type} (configuration : DrvC_Installation.Configuration F C)
 (D : aspis_core.digest.Digest32 H)
 (pub : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
 (publicBytes proof : Slice U8) (k : Usize) (hash : H) (ctx : NHL_Tx1Stages.Context)
 (run : NHL_Tx1Stages.beforeQuery
   (DrvC_Installation.currentInstalled (F3V_Install.configuration configuration))
   (verifier.candidate.prepare (DrvC_Installation.currentInstalled (F3V_Install.configuration configuration)))
   D pub publicBytes proof k hash none=ok (.Ok ctx))
 (base : Port3_NativeQueryBody.Ops) (qPlace gPlace : Nat) :
 NFG_QueryLoopDefs.run
   (NFS_QueryLoopRoot.child base proof (Tx1Q_Carriers.prepared ctx.prepared)
     (Tx1Q_Carriers.arr Tx1Q_Carriers.e ctx.scratch) (Tx1Q_Carriers.geometry ctx.geometry) qPlace gPlace)
   10#usize 10 (.Ok (Tx1Q_Carriers.accumulator ctx.accumulator,Tx1Q_Carriers.pending ctx.pending))=
 Port3_NativeQueryBody.verifier.candidate.query_loop (NFS_QueryOps.installed base)
   proof (Tx1Q_Carriers.prepared ctx.prepared) (Tx1Q_Carriers.accumulator ctx.accumulator)
   (Tx1Q_Carriers.arr Tx1Q_Carriers.e ctx.scratch) none (Tx1Q_Carriers.geometry ctx.geometry)
   (Tx1Q_Carriers.pending ctx.pending) 10#usize := by
 have domain := NHS_ContextDomains.source configuration D pub publicBytes proof k hash ctx run
 exact NFS_QueryLoopRoot.tx1 base proof (Tx1Q_Carriers.prepared ctx.prepared)
   (Tx1Q_Carriers.accumulator ctx.accumulator) (Tx1Q_Carriers.arr Tx1Q_Carriers.e ctx.scratch)
   (Tx1Q_Carriers.geometry ctx.geometry) (Tx1Q_Carriers.pending ctx.pending) qPlace gPlace
   domain.2.1 domain.2.2.1 domain.2.2.2
#print axioms source
end AspisR1.NHS_ContextQuery
