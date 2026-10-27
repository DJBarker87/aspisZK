import KSA_Checks
open Aeneas Aeneas.Std Result XRn_Join_Release XRn_Join_FieldExternal
set_option autoImplicit false
namespace KSA

def mixed : aspis_core.field.QM31 := ⟨⟨1#u32,0#u32⟩,⟨1#u32,0#u32⟩⟩
def rawMixed : aspis_core.field.QM31 := ⟨⟨4294967295#u32,0#u32⟩,⟨4294967295#u32,0#u32⟩⟩
def mixedResult : aspis_core.field.QM31 := ⟨⟨3#u32,1#u32⟩,⟨2147483645#u32,0#u32⟩⟩
theorem mixed_value : aspis_core.field.wide_exact.WideExact.mul_qm31
    (⟨oldQ mixed,oldQ qzero⟩ : XRn_Join_Wide) rawMixed =
    ok (⟨oldQ mixedResult,oldQ qzero⟩ : XRn_Join_Wide) := by rfl
#print axioms mixed_value
end KSA
