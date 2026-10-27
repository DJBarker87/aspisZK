import R1Z.PV_Canon_QAdd
import R1Z.PV_Canon_QMul
import R1Z.PV_Canon_Constructors
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_Canon
open Aeneas Aeneas.Std Result ProverRwFull
/-- Owned low-degree-first Horner specification. No shipped equality is claimed. -/
def horner (x : aspis_core.field.QM31) : List aspis_core.field.QM31 → Result aspis_core.field.QM31
  | [] => .ok ProverRwP7CurrentFieldSource.aspis_core.field.QM31.ZERO
  | c::cs => do
    let tail ← horner x cs
    let product ← ProverRwP7CurrentFieldSource.aspis_core.field.QM31.mul x tail
    ProverRwP7CurrentFieldSource.aspis_core.field.QM31.add c product
 theorem horner_canonical (x : aspis_core.field.QM31) (hx : Q x)
    (coefficients : List aspis_core.field.QM31) (hc : ∀ c ∈ coefficients, Q c) :
    ∃ z, horner x coefficients = .ok z ∧ Q z := by
  induction coefficients with
  | nil => exact ⟨_,rfl,current_qzero⟩
  | cons c cs ih =>
    obtain ⟨tail,ht,hct⟩ := ih (fun z hz => hc z (List.mem_cons_of_mem c hz))
    obtain ⟨product,hp,hcp⟩ := current_qmul x tail hx hct
    obtain ⟨out,ho,hco⟩ := current_qadd c product (hc c (by simp)) hcp
    exact ⟨out,by simp only [horner,ht,hp,ho,bind_tc_ok],hco⟩
#print axioms horner_canonical
end R1Z.PV_Canon
