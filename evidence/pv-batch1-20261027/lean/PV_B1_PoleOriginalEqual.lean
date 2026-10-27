import PV_B1_PoleOriginal
set_option autoImplicit false
noncomputable section
namespace PV_B1_PoleOriginalEqual
open Aeneas Aeneas.Std Result PV_B1_PoleOriginal
local instance : DecidableEq aspis_core.field.QM31 := Classical.decEq _

theorem source (a b : aspis_core.field.QM31) :
    reference.equal a b = ok (decide (a=b)) := by
  rcases a with ⟨⟨a0,a1⟩,⟨a2,a3⟩⟩
  rcases b with ⟨⟨b0,b1⟩,⟨b2,b3⟩⟩
  by_cases h0 : a0=b0 <;> by_cases h1 : a1=b1 <;>
    by_cases h2 : a2=b2 <;> by_cases h3 : a3=b3 <;>
    simp_all [reference.equal]
#print axioms source
end PV_B1_PoleOriginalEqual
