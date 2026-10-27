import XRy_PrepareRawScratch
open Aeneas Aeneas.Std Result
open XRo_Join_Carriers
set_option autoImplicit false
noncomputable section
namespace XRy_PreparePowers

def exceptClaim : AspisR1PublicPreparation.PreparedScratchModel.Boundaries where
 sampling := XRo_Join_Installed.actual.sampling
 powers := AspisR1ClaimPreparedBridge.powersPublic
 claim := XRo_Join_PreparedBoundaries.cachedClaim

theorem gamma_canonical {H : Type} (D : C.D H) (before after : C.T H)
 (row : U8) (payload : Slice U8) (out : C.E)
 (h : AspisR1PublicPreparation.PreparedModel.scalar XRo_Join_Installed.actual.sampling
   D before row payload true=ok (out,after)) : XRy_WideMultiply.Canonical out :=
 AspisR1ClaimPreparedBridge.scalar_candidate_gamma_canonical
   XRo_Join_Installed.actual.sampling D before after row payload out h

theorem change_powers {H : Type} (D : C.D H) (sem : C.Sem H) (v : C.View) (hash : H)
 (g : Array C.E 29#usize) :
 AspisR1PublicPreparation.PreparedScratchModel.prepare XRy_PrepareRawScratch.boundaries D sem v hash g =
 AspisR1PublicPreparation.PreparedScratchModel.prepare exceptClaim D sem v hash g := by
 unfold AspisR1PublicPreparation.PreparedScratchModel.prepare
 simp only [XRy_PrepareRawScratch.boundaries,exceptClaim]
 apply (bind_eq_iff _ _ _).mpr
 intro state hs
 apply (bind_eq_iff _ _ _).mpr
 intro t ht
 apply (bind_eq_iff _ _ _).mpr
 rintro ⟨gamma,t1⟩ hg
 have hc := gamma_canonical D t t1 27#u8 v.y1 gamma hg
 simp only [XRy_PowersPublic.powers 29#usize gamma hc]

theorem prepare (low : XRq_SamplerInterface.Low)
 (leaf : ∀ b, low b=AspisR1Post25Sampler.sampler.low_base_p_digits b)
 {H : Type} (D : C.D H) (sem : C.Sem H) (v : C.View) (hash : H)
 (g : Array C.E 29#usize) :
 mapR (fun p => (inner cprepared ce p.1,p.2))
   (XRy_NarrowPrepare.prepare low (ed D) (es sem) (eview v) hash g) =
 AspisR1PublicPreparation.PreparedScratchModel.prepare exceptClaim D sem v hash g :=
 (XRy_PrepareRawScratch.prepare low leaf D sem v hash g).trans (change_powers D sem v hash g)

#print axioms gamma_canonical
#print axioms change_powers
#print axioms prepare
end XRy_PreparePowers
end
