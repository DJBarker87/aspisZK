import R1TrailingStateFrame

/-! Literal P3 opening-domain frame, matching the flattened byte order
in Transcript::new. This is a byte model, not Rust execution refinement. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.OpeningReseedFrame
open FS2.Duplex
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.UniformStateFirstHit

/-- ASCII `UNPROVED:R1:PRIVATE-SALTED:P3`. -/
def domain : Bytes :=
  [85, 78, 80, 82, 79, 86, 69, 68, 58, 82, 49, 58, 80, 82, 73,
   86, 65, 84, 69, 45, 83, 65, 76, 84, 69, 68, 58, 80, 51]

def frame (tag : Byte) (s : State) : Bytes :=
  TrailingStateFrame.frame (domain ++ [tag]) s

theorem frame_length (tag : Byte) (s : State) : (frame tag s).length = 62 := by
  simp [frame, TrailingStateFrame.frame, domain, bytes_length]

def addr {L : Nat} (tag : Byte) (hL : 62 ≤ L) (s : State) : Addr L :=
  Addr.ofBytes (frame tag s) (by rw [frame_length]; exact hL)

theorem addr_bytes {L : Nat} (tag : Byte) (hL : 62 ≤ L) (s : State) :
    (addr tag hL s).toBytes = domain ++ [tag] ++ bytes s := by
  rw [addr, Addr.toBytes_ofBytes]
  rfl

theorem tailState_addr {L : Nat} (tag : Byte) (hL : 62 ≤ L) (s : State) :
    TrailingStateFrame.tailState (addr tag hL s) = some s :=
  TrailingStateFrame.tailState_frameAddr (domain ++ [tag]) s _

theorem addr_length {L : Nat} (tag : Byte) (hL : 62 ≤ L) (s : State) :
    (addr tag hL s).toBytes.length = 62 := by
  rw [addr, Addr.toBytes_ofBytes, frame_length]

theorem frame_binding (tag tag' : Byte) (s s' : State)
    (h : frame tag s = frame tag' s') : tag = tag' ∧ s = s' := by
  change (domain ++ [tag]) ++ bytes s = (domain ++ [tag']) ++ bytes s' at h
  rw [List.append_assoc, List.append_assoc] at h
  have h' := List.append_cancel_left h
  have hc : tag = tag' ∧ bytes s = bytes s' := List.cons.inj h'
  exact ⟨hc.1, bytes_injective hc.2⟩

#print axioms frame_length
#print axioms addr_bytes
#print axioms tailState_addr
#print axioms addr_length
#print axioms frame_binding
end AspisR1.OpeningReseedFrame
end
