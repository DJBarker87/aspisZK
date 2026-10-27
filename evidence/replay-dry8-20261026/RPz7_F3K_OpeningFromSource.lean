import RPz7_F3K_OpeningCalls
import RPz7_F3J_OpeningPayloads
import RPz7_PAln_OpeningStages
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3K_OpeningFromSource
open Aeneas Aeneas.Std Result
open AspisR1PublicPreparation
open AspisR1CurrentCaller InstalledPreparation BorrowedClaimPrepared OriginalSerializerInstallation
open MultiproofConeCanonical OraclePortCompactDraft

theorem from_double {Hash : Type} (D : AspisR1PublicPreparation.aspis_core.Digest32 Hash)
    (proof semantic y1 : Slice U8) (v : AspisR1CurrentCaller.verifier.View)
    (accepted : sourceView proof semantic y1=ok (.Ok v))
    (p : Parsed) (wire : p.wire=bytesOf proof.val)
    (y1Frame : bytesOf v.y1.val=expand 29 (slice (bytesOf proof.val) 7031 464))
    (sem : AspisR1PublicPreparation.r1_semantic.Verified Hash) (hash : Hash)
    (out : AspisR1PublicPreparation.verifier.Prepared)
    (scratch : Array AspisR1PublicPreparation.aspis_core.field.WideExact 29#usize)
    (double : PAln_OpeningStages.Double closedHashBoundaries D sem (retainedView v) hash out scratch) :
    ∃ c : F3K_OpeningCalls.Calls D closedHashBoundaries.sampling AspisS1M31Embedding.Total.embed (retainedView v) p,
      AspisR1PublicPreparation.transcript.Transcript.new D hash sem.transcript.state (retainedView v).variant=ok c.t0 ∧
      ∃ claim,out=PreparedScratchReachability.output sem (retainedView v) c.gamma c.kappa
        (Array.make 2#usize [c.alpha0,c.alpha1]) c.rho c.queries claim c.t6 ∧
        closedHashBoundaries.powers 29#usize c.gamma=ok scratch ∧
        closedHashBoundaries.claim D sem (retainedView v).y1 (retainedView v).inactive scratch c.kappa=ok (.Ok claim) := by
  obtain ⟨t0,t1,t2,t3,t4,t5,t6,inactive,root,bytes1,bytes2,gamma,kappa,a0,a1,rho,queries,claim,
    seed,first,serialized,second,third,unwrapped,extended1,extended2,fourth,query,last,powers,claimed,same⟩ := double
  have sourceBytes : OriginalSerializerInstallation.sourceBytes (retainedView v).inactive=ok inactive := serialized
  have frames := F3J_OpeningPayloads.selected proof semantic y1 v accepted p wire y1Frame
    root bytes1 bytes2 unwrapped extended1 extended2
  have f28 := F3K_InactivePhysical.row proof semantic y1 v accepted inactive sourceBytes p wire
  have query' : QueriesModel.queries
      (Query31ConcreteMaterializedSchedule.concreteBoundaries Query31ConcreteDriverTraceFacts.sourceDefaultState
        AspisS1M31Embedding.Total.embed) D t4 31#u8 (retainedView v).final_message=ok (.Ok queries,t5) := query
  let c : F3K_OpeningCalls.Calls D closedHashBoundaries.sampling AspisS1M31Embedding.Total.embed (retainedView v) p :=
    { t0:=t0,t1:=t1,t2:=t2,t3:=t3,t4:=t4,t5:=t5,t6:=t6,
      inactive:=inactive,second:=bytes2,gamma:=gamma,kappa:=kappa,alpha0:=a0,alpha1:=a1,rho:=rho,queries:=queries,
      firstCall:=first,inactiveCall:=serialized,secondCall:=second,thirdCall:=third,fourthCall:=fourth,
      queryCall:=query',rhoCall:=last,
      frame27:=frames.1,frame28:=f28,frame29:=frames.2.1,frame30:=frames.2.2.1,
      frame31:=frames.2.2.2.1,frame32:=frames.2.2.2.2 }
  exact ⟨c,seed,claim,same,powers,claimed⟩

#print axioms from_double
end AspisR1.F3K_OpeningFromSource
end
