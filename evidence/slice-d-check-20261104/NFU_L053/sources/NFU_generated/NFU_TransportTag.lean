import NFQ_Transport
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace NFU_TransportTag
def reference : NFQ_Transport.V → U8
  | .S1 => 1#u8 | .S2 => 2#u8 | .D => 3#u8

theorem model (v : NFQ_Transport.V) :
    AspisR1PublicPreparation.transport.Variant.tag v = ok (reference v) := by
  cases v <;> rfl

theorem canonical_range (v : NFQ_Transport.V) :
    1 ≤ (reference v).val ∧ (reference v).val ≤ 3 := by
  cases v <;> decide

theorem deployed_s2 : reference .S2 = 2#u8 := rfl
#print axioms model
#print axioms canonical_range
#print axioms deployed_s2
end NFU_TransportTag
