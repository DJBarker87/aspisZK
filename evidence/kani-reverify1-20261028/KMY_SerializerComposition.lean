import KMY_WindowComposition
set_option autoImplicit false
namespace KMY_SerializerComposition
open KMX_CopyMeaning KMY_WindowComposition

/-- Byte projection asserted by both six-WideExact harnesses. -/
def wideByte (raw : Nat → Nat → Nat → Nat) (j : Nat) : Nat :=
  raw (j/32) ((j%32)/4) (j%4)

theorem wide_six (raw : Nat → Nat → Nat → Nat) (before : Nat → Nat)
    (j : Nat) (bound : j < 192) :
    windows (wideByte raw) before 0 32 6 j =
      raw (j/32) ((j%32)/4) (j%4) := by
  rw [windows_spec, if_pos (by omega)]
  rfl

/-- Exact local append byte assertion. The length is carried separately;
allocation, initialized prefix and source-association remain Rust premises. -/
theorem append_window {α : Type} (source before : Nat → α)
    (len size j : Nat) (bound : j < len+size) :
    window source before len size j =
      if j < len then before j else source (j-len) := by
  rw [window_spec]
  by_cases h : j < len
  · rw [if_pos h, if_neg (by omega)]
  · rw [if_neg h, if_pos (by omega)]

theorem append_length {α : Type} (dst src : List α) :
    (appendLoop dst src).length = dst.length + src.length := by
  rw [append_spec, List.length_append]

/-- The physical proof/public sizes affect oracle argument checks, but not
this byte composition. The original JoinedOracle checks are separate. -/
theorem joined_digest (body hp hu answer : Nat → Nat) (j : Nat) :
    window answer (window hu (window hp body 16 32) 48 32) 1736 32 j =
      if 16 ≤ j ∧ j < 48 then hp (j-16)
      else if 48 ≤ j ∧ j < 80 then hu (j-48)
      else if j < 1736 then body j
      else if j < 1768 then answer (j-1736) else body j := by
  simp only [window_spec]
  by_cases a : 16 ≤ j ∧ j < 48
  · have b : ¬ (48 ≤ j ∧ j < 48+32) := by omega
    have c : ¬ (1736 ≤ j ∧ j < 1736+32) := by omega
    simpa only [if_pos a, if_neg b, if_neg c]
  · by_cases b : 48 ≤ j ∧ j < 80
    · have c : ¬ (1736 ≤ j ∧ j < 1736+32) := by omega
      have b' : 48 ≤ j ∧ j < 48+32 := by omega
      simp only [if_neg a, if_pos b, if_pos b', if_neg c]
    · have a' : ¬ (16 ≤ j ∧ j < 16+32) := by omega
      have b' : ¬ (48 ≤ j ∧ j < 48+32) := by omega
      simp only [if_neg a, if_neg b, if_neg a', if_neg b']
      by_cases c : j < 1736
      · rw [if_pos c, if_neg (by omega)]
      · rw [if_neg c]
        by_cases d : j < 1768
        · rw [if_pos d, if_pos (by omega)]
        · rw [if_neg d, if_neg (by omega)]

#print axioms wide_six
#print axioms append_window
#print axioms append_length
#print axioms joined_digest
end KMY_SerializerComposition
