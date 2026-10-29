import PV_L1D_Logged
set_option autoImplicit false
namespace PV_L1D_Logged
instance {α : Type} : Coe (Aeneas.Std.Result α) (Logged α) := ⟨lift⟩
theorem erase_coe {α : Type} (r : Aeneas.Std.Result α) :
    erase (r : Logged α) = r := rfl
#print axioms erase_coe
end PV_L1D_Logged
