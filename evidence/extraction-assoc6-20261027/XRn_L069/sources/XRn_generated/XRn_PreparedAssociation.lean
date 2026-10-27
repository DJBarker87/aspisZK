import XRn_PreparedCuts
import XRn_PreparedScalars
open Aeneas Aeneas.Std Result
open XRk_Release XRn_Carriers
set_option autoImplicit false
namespace XRn_PreparedAssociation
/-- SAME emitted accepted run, SAME gamma/kappa, and the cohort's actual
scalar definitions instantiated with the explicitly release-backed dictionary.
This does not identify that dictionary with the deployed installation. -/
theorem prefix {H : Type} (D : aspis_core.digest.Digest32 H)
 (sem : r1_semantic.Verified H) (v : verifier.View) (hash : H)
 (old scratch : Array C.E 29#usize) (out : verifier.Prepared)
 (run : verifier.Prepared.new D sem v hash old=ok (.Ok out,scratch)) :
 ∃ (start t1 : transcript.Transcript H) (inactiveBytes : Array U8 32#usize)
   (t2 : transcript.Transcript H) (alpha0 : C.E) (t3 : transcript.Transcript H),
   AspisR1PublicPreparation.transcript.Transcript.new (cd D) hash sem.transcript.state (cv v.variant)=ok (ct start) ∧
   AspisR1PublicPreparation.PreparedModel.scalar XRn_PreparedBoundaries.sampling
     (cd D) (ct start) 27#u8 v.y1 true=ok (out.gamma,ct t1) ∧
   aspis_core.field.wide_exact.WideExact.to_le_bytes v.inactive=ok inactiveBytes ∧
   AspisR1PublicPreparation.PreparedModel.scalar XRn_PreparedBoundaries.sampling
     (cd D) (ct t1) 28#u8 (Array.to_slice inactiveBytes) false=ok (out.kappa,ct t2) ∧
   AspisR1PublicPreparation.PreparedModel.scalar XRn_PreparedBoundaries.sampling
     (cd D) (ct t2) 29#u8 v.round0 false=ok (alpha0,ct t3) := by
 obtain ⟨start,t1,bs,t2,alpha0,t3,hs,hg,hbs,hk,ha⟩ := XRn_PreparedCuts.source D sem v hash old scratch out run
 refine ⟨start,t1,bs,t2,alpha0,t3,?_,?_,hbs,?_,?_⟩
 · have bridge := XRn_Transcript.start (cd D) hash sem.transcript.state (cv v.variant)
   simp only [ed_cd,ev_cv] at bridge
   rw [←bridge,hs]
   rfl
 · have bridge := XRn_PreparedScalars.scalar (cd D) (ct start) 27#u8 v.y1 true
   simp only [ed_cd,et_ct] at bridge
   rw [←bridge,hg]
   rfl
 · have bridge := XRn_PreparedScalars.scalar (cd D) (ct t1) 28#u8 (Array.to_slice bs) false
   simp only [ed_cd,et_ct] at bridge
   rw [←bridge,hk]
   rfl
 · have bridge := XRn_PreparedScalars.scalar (cd D) (ct t2) 29#u8 v.round0 false
   simp only [ed_cd,et_ct] at bridge
   rw [←bridge,ha]
   rfl
#print axioms prefix
end XRn_PreparedAssociation
