import NBV_WindowFrame
import KMX_CopyMeaning

set_option autoImplicit false
namespace AspisR1.NBV_CopyComposition

/-- Lift an explicit element-copy window to its relative value image. This
uses KMX's checked value law; it does not assert Rust pointer refinement. -/
theorem window_value {α : Type} (memory window : Nat → α) (base count c : Nat)
    (inside : c < count) :
    KMX_CopyMeaning.loop (fun k => window (k-base)) memory base count (base+c) =
      window c := by
  rw [KMX_CopyMeaning.loop_spec]
  have range : base ≤ base+c ∧ base+c < base+count := by omega
  simp only [if_pos range,Nat.add_sub_cancel_left]

/-- Disjoint physical openings preserve every coordinate, for arbitrary
surrounding bytes, through the exact KMX value law. -/
theorem opening_frame {α : Type} (memory source : Nat → α)
    (i j c : Nat) (different : i ≠ j) (byte : c < 832) :
    KMX_CopyMeaning.loop source memory (10055+832*j) 832
      (10055+832*i+c) = memory (10055+832*i+c) := by
  apply KMX_CopyMeaning.copy_frame
  have disjoint := NBV_WindowFrame.opening_disjoint i j c different byte
  omega

/-- Adjacent checked windows compose into one physical range, with every
outside coordinate framed. No whole-buffer native execution is hypothesised. -/
theorem adjacent_windows {α : Type} (source memory : Nat → α)
    (base first second : Nat) :
    KMX_CopyMeaning.loop source
      (KMX_CopyMeaning.loop source memory base first) (base+first) second =
    KMX_CopyMeaning.loop source memory base (first+second) := by
  funext k
  simp only [KMX_CopyMeaning.loop_spec]
  by_cases later : base+first ≤ k ∧ k < base+first+second
  · have whole : base ≤ k ∧ k < base+(first+second) := by omega
    simp only [if_pos later,if_pos whole]
  · by_cases earlier : base ≤ k ∧ k < base+first
    · have whole : base ≤ k ∧ k < base+(first+second) := by omega
      simp only [if_neg later,if_pos earlier,if_pos whole]
    · have outside : ¬(base ≤ k ∧ k < base+(first+second)) := by omega
      simp only [if_neg later,if_neg earlier,if_neg outside]

#print axioms window_value
#print axioms opening_frame
#print axioms adjacent_windows
end AspisR1.NBV_CopyComposition
