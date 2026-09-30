import AspisV8R19.CausalDuplexCollisionBound
import AspisV8R19.SourceOraclePrograms

/-! Exact 32-byte-prefix facts for the selected duplex primitives.

These facts justify the deterministic implication from an address collision
to the blocked-state event.  They say nothing about the distribution of the
current state or about correspondence with the complete Rust callback. -/
set_option autoImplicit false
namespace AspisV8R19.SourceFramePrefix

open DuplexFrames SourceDuplexStep SourceOraclePrograms
open CausalDuplexCollisionBound

theorem squeeze_take32 (s : State) :
    (squeeze (bytes s)).take 32 = bytes s := by
  have hs : (bytes s).length = 32 := bytes_length s
  simp [squeeze, List.take_append, hs,
    List.take_of_length_le (by omega : (bytes s).length ≤ 32)]

theorem advance_take32 (s : State) :
    (advance (bytes s)).take 32 = bytes s := by
  have hs : (bytes s).length = 32 := bytes_length s
  simp [advance, List.take_append, hs,
    List.take_of_length_le (by omega : (bytes s).length ≤ 32)]

theorem absorb_take32 (s : State) (label : DuplexFrames.Byte) (data : Bytes) :
    (absorb (bytes s) label data).take 32 = bytes s := by
  have hs : (bytes s).length = 32 := bytes_length s
  simp [absorb, List.take_append, hs,
    List.take_of_length_le (by omega : (bytes s).length ≤ 32)]

theorem grind_take32 (s : State) (nonce : Bytes) :
    (grind (bytes s) nonce).take 32 = bytes s := by
  have hs : (bytes s).length = 32 := bytes_length s
  simp [grind, List.take_append, hs,
    List.take_of_length_le (by omega : (bytes s).length ≤ 32)]

theorem squeeze_calls_prefixed (H : Bytes → State) (s : State) :
    ∀ address ∈ (calls H s).map Prod.fst,
      address.take 32 = bytes s := by
  intro address h
  simp only [calls, List.map_cons, List.map_nil, List.mem_cons,
    List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl
  · exact squeeze_take32 s
  · exact advance_take32 s

theorem absorb_call_prefixed (s : State) (label : DuplexFrames.Byte)
    (data : Bytes) :
    ∀ address ∈ [absorb (bytes s) label data],
      address.take 32 = bytes s := by
  intro address h
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  subst address
  exact absorb_take32 s label data

theorem squeeze_collision_implies_blocked
    (prior : List Bytes) (H : Bytes → State) (s : State)
    (collision : ∃ address ∈ (calls H s).map Prod.fst, address ∈ prior) :
    bytes s ∈ priorPrefixes prior :=
  frame_collision_implies_blocked prior ((calls H s).map Prod.fst) s
    (squeeze_calls_prefixed H s) collision

theorem absorb_collision_implies_blocked
    (prior : List Bytes) (s : State) (label : DuplexFrames.Byte) (data : Bytes)
    (collision : absorb (bytes s) label data ∈ prior) :
    bytes s ∈ priorPrefixes prior :=
  frame_collision_implies_blocked prior [absorb (bytes s) label data] s
    (absorb_call_prefixed s label data)
    ⟨absorb (bytes s) label data, by simp, collision⟩

#print axioms squeeze_take32
#print axioms advance_take32
#print axioms absorb_take32
#print axioms grind_take32
#print axioms squeeze_calls_prefixed
#print axioms absorb_call_prefixed
#print axioms squeeze_collision_implies_blocked
#print axioms absorb_collision_implies_blocked

end AspisV8R19.SourceFramePrefix
