import NFQ_RowShape
import NFQ_Transport
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace NFU_PacketDomains
/-- These are the full row payloads, including message-free rows. -/
def payloadSize (row : Nat) : Nat :=
  if row = 2 ∨ row = 14 then 32
  else if 15 ≤ row ∧ row ≤ 24 then 896
  else if row = 25 then 3712
  else if row = 26 then 928 else 0

theorem payload_bound (row : Nat) : payloadSize row ≤ 3712 := by
  unfold payloadSize
  split <;> (try omega)
  split <;> (try omega)
  split <;> (try omega)
  split <;> omega

theorem framed_bound (row : Nat) : 5 + payloadSize row ≤ 3717 := by
  have h := payload_bound row
  omega

theorem compact_payload_bound (row : Nat) : payloadSize row / 2 ≤ 1856 := by
  have h := payload_bound row
  omega

theorem payload_aligned (row : Nat) : payloadSize row % 32 = 0 := by
  unfold payloadSize
  split <;> (try decide)
  split <;> (try decide)
  split <;> (try decide)
  split <;> decide

theorem low_window (count index : Nat) (inside : index < count / 16) :
    16 * index + 16 ≤ count := by omega

theorem expansion_window (count index : Nat) (inside : index < count / 16) :
    32 * index + 32 ≤ 2 * count := by omega

theorem expansion_disjoint (i j : Nat) (before : i < j) :
    32 * i + 32 ≤ 32 * j := by omega

theorem checkpoint_s2 :
    NFQ_Reference.checkpoint_size_ref (NFQ_Transport.code .S2) = ok 1768#usize := by
  rfl
#print axioms payload_bound
#print axioms framed_bound
#print axioms compact_payload_bound
#print axioms payload_aligned
#print axioms low_window
#print axioms expansion_window
#print axioms expansion_disjoint
#print axioms checkpoint_s2
end NFU_PacketDomains
