import PV_B1_PoleOriginalEqual
set_option autoImplicit false
noncomputable section
namespace PV_B1_OriginalEqualTotal
open Aeneas Aeneas.Std Result PV_B1_PoleOriginal
local instance : DecidableEq aspis_core.field.QM31 := Classical.decEq _

theorem total (a b : aspis_core.field.QM31) :
    ∃ answer, reference.equal a b=ok answer := ⟨_,PV_B1_PoleOriginalEqual.source a b⟩
#print axioms total
end PV_B1_OriginalEqualTotal
