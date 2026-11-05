import NHW_QueryLoop
import NHS_ContextQuery
set_option autoImplicit false
noncomputable section
namespace AspisR1.NHW_ContextQuery
open Aeneas Aeneas.Std Result AspisR1CurrentCaller

theorem split_eq (ops : Ops) {H : Type} (first : NHL_EmittedTx1.Prepare H)
 (D : aspis_core.digest.Digest32 H)
 (pub : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
 (publicBytes proof : Slice U8) (k : Usize) (hash : H) (ctx : NHL_Tx1Stages.Context)
 (run : NHL_Tx1Stages.beforeQuery ops first D pub publicBytes proof k hash none=ok (.Ok ctx)) :
 k=10#usize := by
 unfold NHL_Tx1Stages.beforeQuery at run
 split at run
 · cases run
 · rename_i h
   simpa [compact.SPLIT] using h

/-- The actual deployed leaves and NFS agree on the SAME reached Context.
This replaces the impossible unrestricted dictionary equality with the exact
full-Result, caller-domain transport requested by the driver. -/
theorem source {C H : Type} (missing : IDa_Deployed.Uninstalled C) (err : C)
 (r : NP6_StdModel.Reservation)
 (D : aspis_core.digest.Digest32 H)
 (pub : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
 (publicBytes proof : Slice U8) (k : Usize) (hash : H) (ctx : NHL_Tx1Stages.Context)
 (run : NHL_Tx1Stages.beforeQuery
   (DrvC_Installation.currentInstalled (F3V_Install.configuration (NHW_DeployedQuery.configuration missing err r)))
   (verifier.candidate.prepare (DrvC_Installation.currentInstalled (F3V_Install.configuration (NHW_DeployedQuery.configuration missing err r))))
   D pub publicBytes proof k hash none=ok (.Ok ctx))
 (qPlace gPlace : Nat) :
 (DrvC_Installation.currentInstalled (F3V_Install.configuration (NHW_DeployedQuery.configuration missing err r))).op7
   proof ctx.prepared ctx.accumulator ctx.scratch none ctx.geometry ctx.pending k=
 Tx1Q_Install.result (fun x : Tx1Q_Carriers.S.A × Tx1Q_Carriers.S.B =>
   (Tx1Q_Carriers.unAccumulator x.1,Tx1Q_Carriers.unPending x.2))
   (NFG_QueryLoopDefs.run
     (NFS_QueryLoopRoot.child
       (NHW_QueryDictionary.model (NHW_DeployedQuery.configuration missing err r).query)
       proof (Tx1Q_Carriers.prepared ctx.prepared) (Tx1Q_Carriers.arr Tx1Q_Carriers.e ctx.scratch)
       (Tx1Q_Carriers.geometry ctx.geometry) qPlace gPlace)
     10#usize 10 (.Ok (Tx1Q_Carriers.accumulator ctx.accumulator,Tx1Q_Carriers.pending ctx.pending))) := by
 have split := split_eq _ _ D pub publicBytes proof k hash ctx run
 subst k
 have domain := NHS_ContextDomains.source (NHW_DeployedQuery.configuration missing err r)
   D pub publicBytes proof 10#usize hash ctx run
 have loop := NHW_QueryLoop.tx1 (NHW_DeployedQuery.configuration missing err r).query
   proof (Tx1Q_Carriers.prepared ctx.prepared) (Tx1Q_Carriers.accumulator ctx.accumulator)
   (Tx1Q_Carriers.arr Tx1Q_Carriers.e ctx.scratch) (Tx1Q_Carriers.geometry ctx.geometry)
   (Tx1Q_Carriers.pending ctx.pending) domain.2.2.1 domain.2.2.2
 rw [NHW_DeployedStabilize.deployed] at loop
 have consumer := NHS_ContextQuery.source (NHW_DeployedQuery.configuration missing err r)
   D pub publicBytes proof 10#usize hash ctx run
   (NHW_QueryDictionary.model (NHW_DeployedQuery.configuration missing err r).query) qPlace gPlace
 change Tx1Q_Install.query (Tx1Q_QueryBridge.leaves (NHW_DeployedQuery.configuration missing err r).query)
   proof ctx.prepared ctx.accumulator ctx.scratch none ctx.geometry ctx.pending 10#usize=_
 rw [Tx1Q_QueryBridge.query_body]
 rw [loop,←consumer]
#print axioms split_eq
#print axioms source
end AspisR1.NHW_ContextQuery
