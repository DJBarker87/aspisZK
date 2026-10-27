import XSf_A3Powers
open Aeneas Aeneas.Std Result
open XRo_Join_Carriers
set_option autoImplicit false
noncomputable section
namespace XSf_ReachedScratch
open AspisR1ClaimPreparedBridge
open AspisR1PublicPreparation.PreparedScratchReachability

theorem tail_powers {H : Type} (D : C.D H) (sem : C.Sem H) (v : C.View)
 (gamma kappa alpha : C.E) (before : C.T H) (out : C.Prepared) (scratch : XSa_DotRun.Coeff)
 (ht : Tail XRo_Join_Installed.actual D sem v gamma kappa alpha before out scratch) :
 powersPublic 29#usize gamma=ok scratch := by
 cases ht with
 | single hf tail =>
   obtain ⟨queries,afterQueries,last,rho,claim,hq,hr,hp,hc,he⟩ := tail
   exact hp
 | double hf root b1 b2 a1 afterAlpha hroot hb1 hb2 halpha tail =>
   obtain ⟨queries,afterQueries,last,rho,claim,hq,hr,hp,hc,he⟩ := tail
   exact hp

/-- All three canonicality facts and raw powers are conclusions from the
SAME successful prepare, not separately supplied challenge/scratch inputs. -/
theorem produced {H : Type} (D : C.D H) (sem : C.Sem H) (v : C.View) (hash : H)
 (out : C.Prepared) (scratch old : XSa_DotRun.Coeff)
 (run : AspisR1PublicPreparation.PreparedScratchModel.prepare XRo_Join_Installed.actual
   D sem v hash old=ok (.Ok out,scratch)) :
 XRy_WideMultiply.Canonical out.gamma ∧ XRy_WideMultiply.Canonical out.kappa ∧
 XSa_DotRun.canonical scratch ∧ powersPublic 29#usize out.gamma=ok scratch ∧
 XRn_Join_Release.weights.powers 29#usize out.gamma=ok scratch := by
 obtain ⟨start,t1,t2,t3,bytes,gamma,kappa,alpha,hseed,hg,hb,hk,ha,ht⟩ :=
   AspisR1PublicPreparation.PreparedScratchReachability.prepare_success
     XRo_Join_Installed.actual D sem v hash out scratch old run
 have fields := tail_concrete_run XRo_Join_Installed.actual.sampling D sem v gamma kappa alpha t3 out scratch ht
 have hgc := XRy_PreparePowers.gamma_canonical D start t1 27#u8 v.y1 gamma hg
 have hkc := XSf_Reached.kappa D t1 t2 28#u8 (Array.to_slice bytes) kappa hk
 have hp := tail_powers D sem v gamma kappa alpha t3 out scratch ht
 have hs := XSf_A3Powers.observed_weights D start t1 v.y1 gamma scratch hg hp
 rw [←fields.1] at hgc hp hs
 rw [←fields.2.1] at hkc
 exact ⟨hgc,hkc,hs.1,hp,hs.2⟩

#print axioms tail_powers
#print axioms produced
end XSf_ReachedScratch
end
