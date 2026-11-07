import NMC_WindowModels
set_option autoImplicit false
noncomputable section
namespace AspisR1.NMC_Compare
open Aeneas Aeneas.Std Result AspisR1PublicPreparation NMC_Models
theorem qeq_true (a b : Q) : qeq a b=true ↔ a=b := by classical simp [qeq]
theorem peq_true (a b : NLC_Finish.Point) : peq a b=true ↔ a=b := by classical simp [peq]
/-- Direct small emitted comparison law; no field multiplication or numerical
recurrence is unfolded. All four u32 limbs are unrestricted. -/
theorem emitted_eq (a b : Q) :
 aspis_core.field.QM31.Insts.CoreCmpPartialEqQM31.eq a b=ok (qeq a b) := by
 classical
 rcases a with ⟨⟨a0,a1⟩,⟨a2,a3⟩⟩
 rcases b with ⟨⟨b0,b1⟩,⟨b2,b3⟩⟩
 by_cases h0 : a0=b0 <;> by_cases h1 : a1=b1 <;> by_cases h2 : a2=b2 <;> by_cases h3 : a3=b3 <;>
  simp [aspis_core.field.QM31.Insts.CoreCmpPartialEqQM31.eq,
   aspis_core.field.CM31.Insts.CoreCmpPartialEqCM31.eq,qeq,h0,h1,h2,h3]
#print axioms qeq_true
#print axioms peq_true
#print axioms emitted_eq
end AspisR1.NMC_Compare
end
