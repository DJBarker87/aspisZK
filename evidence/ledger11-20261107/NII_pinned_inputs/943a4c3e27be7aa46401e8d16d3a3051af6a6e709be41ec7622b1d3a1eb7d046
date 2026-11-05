import NFW_PreparedResults
set_option autoImplicit false
noncomputable section
namespace AspisR1.NFW_PreparedCalls
open Aeneas Aeneas.Std Result AspisR1PublicPreparation PreparedScratchReachability
/-- Every child call below is extracted from the same successful cohort
producer. These are conclusions of the source execution, not extra child-
success premises added to a native caller. The native producer link is OPEN. -/
theorem calls {H : Type} (B : PreparedScratchModel.Boundaries) (D : aspis_core.Digest32 H)
 (sem : r1_semantic.Verified H) (v : verifier.View) (hash : H)
 (out : verifier.Prepared) (scratch old : Array aspis_core.field.WideExact 29#usize)
 (run : PreparedScratchModel.prepare B D sem v hash old=ok (.Ok out,scratch)) :
 B.powers 29#usize out.gamma=ok scratch ∧
 B.claim D sem v.y1 v.inactive scratch out.kappa=ok (.Ok out.claim) ∧
 ∃ (row : U8) (before afterQueries last : transcript.Transcript H),
  (row=30#u8 ∨ row=31#u8) ∧
  B.sampling.queries D before row v.final_message=ok (.Ok out.queries,afterQueries) ∧
  PreparedModel.scalar_k B.sampling D afterQueries (if row=30#u8 then 31#u8 else 32#u8)
   emptyPayload=ok (out.rho,last) ∧ out.state=last.state := by
 obtain ⟨start,t1,t2,t3,bytes,gamma,kappa,alpha0,hs,hg,hb,hk,ha,tail⟩ :=
  PreparedScratchReachability.prepare_success B D sem v hash out scratch old run
 cases tail with
 | single hf rest =>
  obtain ⟨queries,aq,last,rho,claim,hq,hr,hp,hc,he⟩ := rest
  subst out
  exact ⟨hp,hc,30#u8,t3,aq,last,Or.inl rfl,hq,hr,rfl⟩
 | double hf root b1 b2 alpha1 afterAlpha hroot hb1 hb2 ha1 rest =>
  obtain ⟨queries,aq,last,rho,claim,hq,hr,hp,hc,he⟩ := rest
  subst out
  exact ⟨hp,hc,31#u8,afterAlpha,aq,last,Or.inr rfl,hq,hr,rfl⟩
#print axioms calls
end AspisR1.NFW_PreparedCalls
