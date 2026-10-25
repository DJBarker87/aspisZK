import PAln_OpeningStages
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1.PAln_OutputFields
open AspisR1PublicPreparation PreparedScratchReachability

theorem from_double {H : Type} (B : PreparedScratchModel.Boundaries) (D : aspis_core.Digest32 H)
    (sem : r1_semantic.Verified H) (view : verifier.View) (hash : H)
    (out : verifier.Prepared) (scratch : Array aspis_core.field.WideExact 29#usize)
    (reached : PAln_OpeningStages.Double B D sem view hash out scratch) :
    ∃ (t0 t1 t2 t3 t4 : transcript.Transcript H)
      (inactive : Array U8 32#usize) (bytes2 : alloc.vec.Vec U8)
      (alpha0 alpha1 : aspis_core.field.WideExact),
      PreparedModel.scalar B.sampling D t0 27#u8 view.y1 true=ok (out.gamma,t1) ∧
      B.sampling.toBytes view.inactive=ok inactive ∧
      PreparedModel.scalar B.sampling D t1 28#u8 (Array.to_slice inactive) false=ok (out.kappa,t2) ∧
      PreparedModel.scalar B.sampling D t2 29#u8 view.round0 false=ok (alpha0,t3) ∧
      PreparedModel.scalar B.sampling D t3 30#u8 (alloc.vec.Vec.deref bytes2) false=ok (alpha1,t4) ∧
      out.alpha.val=[alpha0,alpha1] ∧ B.powers 29#usize out.gamma=ok scratch := by
  obtain ⟨t0,t1,t2,t3,t4,t5,t6,inactive,root,bytes1,bytes2,gamma,kappa,alpha0,alpha1,
    rho,queries,claim,seed,g,serialized,k,a,rootCall,first,second,sampled,query,rhoCall,powers,claimed,same⟩ := reached
  subst out
  exact ⟨t0,t1,t2,t3,t4,inactive,bytes2,alpha0,alpha1,g,serialized,k,a,sampled,rfl,powers⟩

#print axioms from_double
end AspisR1.PAln_OutputFields
