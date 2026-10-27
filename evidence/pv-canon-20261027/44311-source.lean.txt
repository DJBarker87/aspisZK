import R1Z.PV_Canon_Horner
import R1Z.PV_Canon_FieldMeaning
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_Canon
open Aeneas Aeneas.Std Result ProverRwFull
 theorem decode_zero : decodeQ ProverRwP7CurrentFieldSource.aspis_core.field.QM31.ZERO = 0 := by
  rw [ProverRwP7CurrentFieldSource.aspis_core.field.QM31.ZERO]
  rfl
 def polynomialValue (x : K) : List aspis_core.field.QM31 → K
  | [] => 0
  | c::cs => decodeQ c + x * polynomialValue x cs
 theorem horner_meaning (x : aspis_core.field.QM31) (hx : Q x)
    (coefficients : List aspis_core.field.QM31) (hc : ∀ c ∈ coefficients, Q c) :
    ∃ z, horner x coefficients = .ok z ∧ Q z ∧ decodeQ z=polynomialValue (decodeQ x) coefficients := by
  induction coefficients with
  | nil => exact ⟨_,rfl,current_qzero,decode_zero⟩
  | cons c cs ih =>
    obtain ⟨tail,ht,hct,hvt⟩ := ih (fun z hz => hc z (List.mem_cons_of_mem c hz))
    obtain ⟨product,hp,hcp,hvp⟩ := current_qmul_meaning x tail hx hct
    obtain ⟨out,ho,hco,hvo⟩ := current_qadd_meaning c product (hc c (by simp)) hcp
    refine ⟨out,by simp only [horner,ht,hp,ho,bind_tc_ok],hco,?_⟩
    rw [hvo,hvp,hvt]
    rfl
#print axioms decode_zero
#print axioms horner_meaning
end R1Z.PV_Canon
