import NHW_ContextQuery
import NHW_CheckpointPort
set_option autoImplicit false
noncomputable section
namespace AspisR1.NHW_ModelWriter
open Aeneas Aeneas.Std Result AspisR1CurrentCaller
open CheckpointBytes3Namespaces
/-- Inversion produces all witnesses from this SAME adopted TX1 acceptance.
It is model-side support, not a replacement for a native prefix certificate. -/
theorem source {C H : Type} (missing : IDa_Deployed.Uninstalled C) (err : C)
 (r : NP6_StdModel.Reservation) (D : aspis_core.digest.Digest32 H) (hash : H)
 (pub : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
 (publicBytes proof : Slice U8) (k : Usize) (saved : alloc.vec.Vec U8)
 (accepted : verifier.candidate.tx1
   (DrvC_Installation.currentInstalled (F3V_Install.configuration (NHW_DeployedQuery.configuration missing err r)))
   D pub publicBytes proof k hash none=ok (.Ok saved)) :
 ∃ p : verifier.Prepared, ∃ a : verifier.Accumulator,
 ∃ domain : NGC_KNE_Caller.WriterDomain (toPrepared (Tx1Q_Carriers.prepared p))
   (toAccumulator (Tx1Q_Carriers.accumulator a)),
 NHW_CheckpointPort.source D p a domain proof publicBytes hash=ok saved := by
 let c := NHW_DeployedQuery.configuration missing err r
 let installed := DrvC_Installation.currentInstalled (F3V_Install.configuration c)
 have slots : Tx1Q_Execution.Slots installed c.reserved c.query c.geometry :=
   ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩
 obtain ⟨run⟩ := Tx1Q_Execution.accepted_generic installed c.reserved c.query c.geometry
   D hash pub publicBytes proof k saved slots accepted
 have fields := NHS_PrepareFields.installed
   (DrvC_Installation.current (F3V_Install.configuration c)) c.boundaries c.std
   D hash pub proof _ run.scratch run.p run.prepare_call
 have newA := (NGC_Initialization.constructor c.stageBase c.reserved .S2).trans run.initial_call
 have initial := NGC_InitialInvariant.initial c.stageBase c.reserved c.reserved
   (Tx1Q_Carriers.prepared run.p) (Tx1Q_Carriers.accumulator run.initial)
   (Tx1Q_Carriers.pending run.pending) fields newA run.pending_call
 have loop := NHW_QueryLoop.tx1 c.query proof (Tx1Q_Carriers.prepared run.p)
   (Tx1Q_Carriers.accumulator run.initial) (Tx1Q_Carriers.arr Tx1Q_Carriers.e run.scratch)
   (Tx1Q_Carriers.geometry run.geometry) (Tx1Q_Carriers.pending run.pending) initial.1 initial.2
 have query : Port3_NativeQueryBody.verifier.candidate.query_loop
   (NFS_QueryOps.installed (NHW_QueryDictionary.model c.query)) proof (Tx1Q_Carriers.prepared run.p)
   (Tx1Q_Carriers.accumulator run.initial) (Tx1Q_Carriers.arr Tx1Q_Carriers.e run.scratch)
   none (Tx1Q_Carriers.geometry run.geometry) (Tx1Q_Carriers.pending run.pending) 10#usize=
   ok (.Ok (Tx1Q_Carriers.accumulator run.out,Tx1Q_Carriers.pending run.after)) := by
   rw [←loop]
   simpa only [c,NHW_DeployedStabilize.deployed] using run.query_call
 obtain ⟨out,flush,domain,_⟩ := NGC_WriterDomain.from_query_loop
   (NHW_QueryDictionary.model c.query) proof (Tx1Q_Carriers.prepared run.p)
   (Tx1Q_Carriers.accumulator run.initial) (Tx1Q_Carriers.accumulator run.out)
   (Tx1Q_Carriers.arr Tx1Q_Carriers.e run.scratch) (Tx1Q_Carriers.geometry run.geometry)
   (Tx1Q_Carriers.pending run.pending) (Tx1Q_Carriers.pending run.after)
   initial.1 initial.2 fields query
 have same := Result.ok.inj (flush.symm.trans run.flush_call)
 subst out
 refine ⟨run.p,{run.out with weights:=⟨run.flushed.val,run.flushed.property⟩},domain,?_⟩
 rw [NHW_CheckpointPort.slot]
 exact run.writer_call
#print axioms source
end AspisR1.NHW_ModelWriter
