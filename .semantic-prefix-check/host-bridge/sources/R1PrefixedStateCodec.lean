import R1TrailingStateFrame

/-! Prefix-checking parser for a byte string ending in a state. -/
set_option autoImplicit false
namespace AspisR1.PrefixedStateCodec

open FS FS2 FS2.Duplex
open AspisV8PairedCommitment AspisV8R19.DuplexFrames
open AspisV8R19.SourceDuplexStep

noncomputable section

def parse {L : Nat} (pre : Bytes) (a : Addr L) : Option State :=
  if a.toBytes.length = pre.length + 32 ∧ a.toBytes.take pre.length = pre then
    some (stateOfBytes (a.toBytes.drop pre.length))
  else none

theorem bytes_stateOfBytes (b : Bytes) (hlen : b.length = 32) :
    bytes (stateOfBytes b) = b := by
  apply List.ext_getElem
  · simp [bytes, hlen]
  · intro i hi hi'
    change (List.ofFn (stateOfBytes b))[i] = b[i]
    rw [List.getElem_ofFn]
    change b[i]?.getD 0 = b[i]
    rw [List.getElem?_eq_getElem hi']
    rfl

theorem parse_frameAddr {L : Nat} (pre : Bytes) (s : State)
    (h : (TrailingStateFrame.frame pre s).length ≤ L) :
    parse pre (TrailingStateFrame.frameAddr pre s h) = some s := by
  have hlen : (TrailingStateFrame.frame pre s).length = pre.length + 32 := by
    simp [TrailingStateFrame.frame, bytes_length]
  have htake : (pre ++ bytes s).take pre.length = pre := by
    calc
      (pre ++ bytes s).take pre.length = pre.take pre.length :=
        List.take_append_of_le_length (l₁ := pre) (l₂ := bytes s)
          (i := pre.length) (Nat.le_refl _)
      _ = pre := List.take_of_length_le (by omega)
  simp only [parse, TrailingStateFrame.frameAddr, Addr.toBytes_ofBytes]
  rw [if_pos ⟨hlen, by simpa [TrailingStateFrame.frame] using htake⟩]
  rw [TrailingStateFrame.frame]
  rw [List.drop_append_of_le_length (by simp)]
  rw [List.drop_eq_nil_of_le (by simp)]
  simpa using (stateOfBytes_bytes s ([] : Bytes))

theorem parse_sound {L : Nat} (pre : Bytes) (a : Addr L) (s : State)
    (h : parse pre a = some s) : a.toBytes = pre ++ bytes s := by
  unfold parse at h
  split at h
  · rename_i hp
    have hs : stateOfBytes (a.toBytes.drop pre.length) = s := Option.some.inj h
    have hdrop : (a.toBytes.drop pre.length).length = 32 := by
      simp [List.length_drop, hp.1]
    have hdrop_eq : a.toBytes.drop pre.length = bytes s := by
      calc
        a.toBytes.drop pre.length = bytes (stateOfBytes (a.toBytes.drop pre.length)) :=
          (bytes_stateOfBytes _ hdrop).symm
        _ = bytes s := by rw [hs]
    calc
      a.toBytes = a.toBytes.take pre.length ++ a.toBytes.drop pre.length :=
        (List.take_append_drop pre.length a.toBytes).symm
      _ = pre ++ bytes s := by rw [hp.2, hdrop_eq]
  · simp at h

#print axioms bytes_stateOfBytes
#print axioms parse_frameAddr
#print axioms parse_sound

end
end AspisR1.PrefixedStateCodec
