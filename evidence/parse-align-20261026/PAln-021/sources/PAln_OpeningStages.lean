import PAln_OpeningReach
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1.PAln_OpeningStages
open AspisR1PublicPreparation PreparedScratchReachability

/-- All opening suffix calls on the two-fold path. The output equation binds
challenges, queries, rho and final state to the SAME returned preparation. -/
def Double {H : Type} (B : PreparedScratchModel.Boundaries) (D : aspis_core.Digest32 H)
    (sem : r1_semantic.Verified H) (view : verifier.View) (hash : H)
    (out : verifier.Prepared) (scratch : Array aspis_core.field.WideExact 29#usize) : Prop :=
  ∃ (t0 t1 t2 t3 t4 t5 t6 : transcript.Transcript H)
    (inactive root : Array U8 32#usize) (bytes1 bytes2 : alloc.vec.Vec U8)
    (gamma kappa alpha0 alpha1 : aspis_core.field.WideExact)
    (rho : aspis_core.field.QM31) (queries : Array U32 22#usize)
    (claim : aspis_core.field.WideExact),
    transcript.Transcript.new D hash sem.transcript.state view.variant=ok t0 ∧
    PreparedModel.scalar B.sampling D t0 27#u8 view.y1 true=ok (gamma,t1) ∧
    B.sampling.toBytes view.inactive=ok inactive ∧
    PreparedModel.scalar B.sampling D t1 28#u8 (Array.to_slice inactive) false=ok (kappa,t2) ∧
    PreparedModel.scalar B.sampling D t2 29#u8 view.round0 false=ok (alpha0,t3) ∧
    core.option.Option.unwrap view.folded_root=ok root ∧
    alloc.vec.Vec.extend_from_slice core.clone.CloneU8
      (alloc.vec.Vec.with_capacity U8 256#usize) (Array.to_slice root)=ok bytes1 ∧
    alloc.vec.Vec.extend_from_slice core.clone.CloneU8 bytes1 view.round1=ok bytes2 ∧
    PreparedModel.scalar B.sampling D t3 30#u8 (alloc.vec.Vec.deref bytes2) false=ok (alpha1,t4) ∧
    B.sampling.queries D t4 31#u8 view.final_message=ok (.Ok queries,t5) ∧
    PreparedModel.scalar_k B.sampling D t5 32#u8 emptyPayload=ok (rho,t6) ∧
    B.powers 29#usize gamma=ok scratch ∧
    B.claim D sem view.y1 view.inactive scratch kappa=ok (.Ok claim) ∧
    out=output sem view gamma kappa (Array.make 2#usize [alpha0,alpha1]) rho queries claim t6

theorem double_of_reached {H : Type} (B : PreparedScratchModel.Boundaries) (D : aspis_core.Digest32 H)
    (sem : r1_semantic.Verified H) (view : verifier.View) (hash : H)
    (out : verifier.Prepared) (scratch : Array aspis_core.field.WideExact 29#usize)
    (variant : view.variant=.S2)
    (reached : Reachable B D sem view hash out scratch) : Double B D sem view hash out scratch := by
  obtain ⟨t0,t1,t2,t3,inactive,gamma,kappa,alpha0,seed,g,serialized,k,a,tail⟩ := reached
  cases tail with
  | single folds tail =>
    rw [variant] at folds
    change (ok 2#usize : Result Usize)=ok 1#usize at folds
    have bad := congrArg UScalar.val (Result.ok.inj folds)
    omega
  | double folds root bytes1 bytes2 alpha1 t4 rootCall first second sampled tail =>
    obtain ⟨queries,t5,t6,rho,claim,query,rhoCall,powers,claimed,same⟩ := tail
    exact ⟨t0,t1,t2,t3,t4,t5,t6,inactive,root,bytes1,bytes2,gamma,kappa,alpha0,alpha1,
      rho,queries,claim,seed,g,serialized,k,a,rootCall,first,second,sampled,query,rhoCall,powers,claimed,same⟩

#print axioms double_of_reached
end AspisR1.PAln_OpeningStages
