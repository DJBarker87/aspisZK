import KMX_CopyMeaning
set_option autoImplicit false
namespace KMY_WindowComposition
open KMX_CopyMeaning

def window {α : Type} (src dst : Nat → α) (pos size : Nat) : Nat → α :=
  loop (fun k => src (k-pos)) dst pos size

theorem window_spec {α : Type} (src dst : Nat → α) (pos size k : Nat) :
    window src dst pos size k =
      if pos ≤ k ∧ k < pos+size then src (k-pos) else dst k :=
  loop_spec _ _ _ _ _

theorem disjoint_frame {α : Type} (a b dst : Nat → α) (p n q m k : Nat)
    (disjoint : p+n ≤ q) (inside : p ≤ k ∧ k < p+n) :
    window b (window a dst p n) q m k = a (k-p) := by
  rw [window_spec, if_neg (by omega), window_spec, if_pos inside]

/-- Exactly the byte postcondition of LPn_step_frame, including arbitrary
pre-state outside the two adjacent 16-byte windows. Bounds and pointer
identity are separate Rust obligations. -/
theorem LPn_step_frame (source before : Nat → Nat) (pos j : Nat) :
    window (fun _ => 0) (window source before pos 16) (pos+16) 16 j =
      if pos ≤ j ∧ j < pos+16 then source (j-pos)
      else if pos+16 ≤ j ∧ j < pos+32 then 0 else before j := by
  rw [window_spec, window_spec]
  by_cases a : pos ≤ j ∧ j < pos+16
  · have b : ¬ (pos+16 ≤ j ∧ j < pos+16+16) := by omega
    simp only [if_pos a, if_neg b]
  · have h : pos+16+16 = pos+32 := by omega
    simp only [if_neg a, h]

/-- Composition of all contiguous equal-size windows; the source is indexed
by final byte position, so serializers can instantiate it with their exact
limb/byte projection. -/
def windows {α : Type} (src dst : Nat → α) (start width : Nat) : Nat → Nat → α
  | 0 => dst
  | n+1 => loop src (windows src dst start width n) (start+width*n) width

theorem windows_spec {α : Type} (src dst : Nat → α) (start width n k : Nat) :
    windows src dst start width n k =
      if start ≤ k ∧ k < start+width*n then src k else dst k := by
  induction n with
  | zero =>
    have h : ¬ (start ≤ k ∧ k < start+width*0) := by omega
    simp only [windows, if_neg h]
  | succ n ih =>
    rw [windows, loop_spec, ih, Nat.mul_succ]
    by_cases a : start+width*n ≤ k ∧ k < start+width*n+width
    · have h : start ≤ k ∧ k < start+(width*n+width) := by omega
      simp only [if_pos a, if_pos h]
    · by_cases b : start ≤ k ∧ k < start+width*n
      · have h : start ≤ k ∧ k < start+(width*n+width) := by omega
        simp only [if_neg a, if_pos b, if_pos h]
      · have h : ¬ (start ≤ k ∧ k < start+(width*n+width)) := by omega
        simp only [if_neg a, if_neg b, if_neg h]

#print axioms window_spec
#print axioms disjoint_frame
#print axioms LPn_step_frame
#print axioms windows_spec
end KMY_WindowComposition
