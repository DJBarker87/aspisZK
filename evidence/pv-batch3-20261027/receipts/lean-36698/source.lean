import PV_B3_BoundedPacket
import PV_B3_QArrayCarrier
namespace PV_B3_RawInputPacket
open Aeneas Aeneas.Std Result PV_B3_FieldTransport PV_B3_QArrayCarrier
set_option autoImplicit false

-- Old-carrier adapters for the actual extracted copies. These are not the
-- missing original Rust/source equations or canonical-domain row laws.
def mask117 (c : Array Old.Q 16#usize) (m : Array Old.Q 10#usize) (g : Old.Q)
    (p : Array Old.Q 10#usize) : Result Old.Q :=
  map toQ (PV_B3_Copy_117.host_arithmetic.state_only_selected_mask_value
    (fromArray c) (fromArray m) (fromQ g) (fromArray p))

theorem mask117_bounded (c : Array Old.Q 16#usize) (m : Array Old.Q 10#usize) (g : Old.Q)
    (p : Array Old.Q 10#usize) : mask117 c m g p =
    map toQ (PV_B3_Mask117Finite.reference (fromArray c) (fromArray m) (fromQ g) (fromArray p)) := by
  unfold mask117
  rw [PV_B3_BoundedPacket.mask117]

def polynomial121 (p : Array Old.Q 28#usize) (x : Old.Q) : Result Old.Q :=
  map toQ (PV_B3_Copy_117.host_arithmetic.evaluate_state_only_polynomial (fromArray p) (fromQ x))

theorem polynomial121_bounded (p : Array Old.Q 28#usize) (x : Old.Q) : polynomial121 p x =
    map toQ (PV_B3_PolynomialFinite.reference (fromArray p) (fromQ x)) := by
  unfold polynomial121
  rw [PV_B3_BoundedPacket.polynomial121]

theorem input_roundtrip {n : Usize} (a : Array Old.Q n) : toArray (fromArray a) = a := right a

theorem nonvacuity117 : ∃ c : Array Old.Q 16#usize, ∃ m : Array Old.Q 10#usize,
    ∃ g : Old.Q, ∃ p : Array Old.Q 10#usize,
      toArray (fromArray c) = c ∧ toArray (fromArray m) = m ∧
      toQ (fromQ g) = g ∧ toArray (fromArray p) = p := by
  let q : Old.Q := toQ PV_B3_Copy_117.aspis_core.field.QM31.ZERO
  exact ⟨Array.repeat 16#usize q, Array.repeat 10#usize q, q, Array.repeat 10#usize q,
    right _, right _, q_right _, right _⟩

#print axioms mask117
#print axioms mask117_bounded
#print axioms polynomial121
#print axioms polynomial121_bounded
#print axioms input_roundtrip
#print axioms nonvacuity117
end PV_B3_RawInputPacket
