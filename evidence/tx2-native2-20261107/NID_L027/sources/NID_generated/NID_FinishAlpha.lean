import NID_ResumeCallerDomain
set_option autoImplicit false
noncomputable section
namespace NID_FinishAlpha
open Aeneas Aeneas.Std Result AspisR1 AspisR1Stage2

def alphaAt (p : verifier.Prepared) (i : Fin 2) : aspis_core.field.wide_exact.WideExact :=
 p.alpha.val[i.val]'(by rw [p.alpha.property];exact i.isLt)

theorem supplied (p : verifier.Prepared) (a : verifier.Accumulator)
 (d : NID_ResumeFields.Domain p a) (i : Fin 2) :
 Array.index_usize p.alpha (Usize.ofNat i.val (by scalar_tac))=ok (alphaAt p i) ∧
 LPi_FieldValues.canonE (FIo_Install.toE (alphaAt p i)) := by
 constructor
 · have hi : i.val<p.alpha.val.length := by rw [p.alpha.property];exact i.isLt
   simp [Array.index_usize,alphaAt,List.getElem?_eq_getElem hi]
 · have member : alphaAt p i ∈ p.alpha.val := by
     exact List.getElem_mem _
   exact NID_ResumeCallerDomain.gamma (alphaAt p i) (d.alpha _ member)

/-- Primitive Prepared finish fields from the same reader-produced pair.
Proof-window canonicality is a separate actual scan/history obligation. -/
theorem primitive (p : verifier.Prepared) (a : verifier.Accumulator)
 (d : NID_ResumeFields.Domain p a) :
 p.variant=.S2 ∧ LPi_FieldValues.canonE (FIo_Install.toE p.claim) ∧
 LPi_FieldValues.canonE (FIo_Install.toE p.kappa) ∧
 (∀ x ∈ p.semantic_alpha.val, NBF_PowerStep.Canonical x) ∧
 (∀ z ∈ p.z.val, NBF_PowerStep.Canonical z.x ∧ NBF_PowerStep.Canonical z.y) := by
 refine ⟨d.variant,NID_ResumeCallerDomain.gamma _ d.claim,
  NID_ResumeCallerDomain.gamma _ d.kappa,?_,?_⟩
 · intro x hx
   exact NID_ResumeCallerDomain.power x (d.semantic x hx)
 · intro z hz
   exact ⟨NID_ResumeCallerDomain.power _ (d.coordinates z hz).1,
    NID_ResumeCallerDomain.power _ (d.coordinates z hz).2⟩
#print axioms supplied
#print axioms primitive
end NID_FinishAlpha
