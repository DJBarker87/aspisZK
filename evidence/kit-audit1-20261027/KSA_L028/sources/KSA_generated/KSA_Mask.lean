import KSA_QpowShape
open Aeneas Aeneas.Std Result XRn_Join_Release XRn_Join_FieldExternal
set_option autoImplicit false
namespace KSA

def scalar (n : U32) : aspis_core.field.QM31 := ⟨⟨n,0#u32⟩,⟨0#u32,0#u32⟩⟩
theorem qpow26 : XRn_Join_qpow (scalar 275#u32) 26 = ok (scalar 1424173331#u32) := by
  rw [qpow26_shape]
  rfl
#print axioms qpow26
end KSA

namespace KSA
open Aeneas Aeneas.Std Result XRn_Join_Release XRn_Join_FieldExternal

def maskPoint : Array aspis_core.field.QM31 10#usize :=
  Array.make 10#usize [qone,qzero,qzero,qzero,qzero,qzero,qzero,qzero,qzero,qzero]
theorem mask_value : aspis_core.state_only_hiding.state_only_selected_mask_value
    (Array.repeat 16#usize qzero) (Array.repeat 10#usize qzero) qone maskPoint =
    ok (scalar 1424173332#u32) := by
  change (do
    let power ← XRn_Join_qpow (scalar 275#u32) 26
    let factor ← aspis_core.field.QM31.add qone power
    let term ← aspis_core.field.QM31.mul factor qone
    aspis_core.field.QM31.add qzero term) = _
  rw [qpow26]
  rfl
#print axioms mask_value
end KSA
