import AspisV8R19.QM31SamplerProgram

set_option autoImplicit false
namespace AspisV8R19.QM31SamplerInvariants
open DuplexFrames SourceDuplexStep QM31SamplerProgram

theorem accepted_limbs_length (H : Bytes → State) (n : Nat) (c : Cursor)
    (xs : List Nat) (h : (limbsRun H n c).2.1 = some xs) : xs.length = n := by
  induction n generalizing c xs with
  | zero => simpa [limbsRun] using congrArg (Option.map List.length) h.symm
  | succ n ih =>
      simp only [limbsRun] at h
      cases ha : (limbRun H 8 c).2.1 with
      | none => simp [ha] at h
      | some a =>
          simp only [ha] at h
          cases ht : (limbsRun H n (limbRun H 8 c).2.2).2.1 with
          | none => simp [ht] at h
          | some tail =>
              have he : a::tail = xs := by simpa [ht] using h
              rw [← he,List.length_cons,ih _ tail ht]

theorem accepted_limbs_canonical (H : Bytes → State) (n : Nat) (c : Cursor)
    (xs : List Nat) (h : (limbsRun H n c).2.1 = some xs) : ∀ a ∈ xs, a < 2147483647 := by
  induction n generalizing c xs with
  | zero => have he : [] = xs := by simpa [limbsRun] using h
            subst xs; simp
  | succ n ih =>
      simp only [limbsRun] at h
      cases ha : (limbRun H 8 c).2.1 with
      | none => simp [ha] at h
      | some a =>
          simp only [ha] at h
          cases ht : (limbsRun H n (limbRun H 8 c).2.2).2.1 with
          | none => simp [ht] at h
          | some tail =>
              have he : a::tail = xs := by simpa [ht] using h
              rw [← he]
              intro b hb
              rcases List.mem_cons.mp hb with hb | hb
              · subst b; exact accepted_limb_canonical H 8 c a ha
              · exact ih _ tail ht b hb

theorem challenge_four_canonical_limbs (H : Bytes → State) (s : State) (xs : List Nat)
    (h : (challengeRun H s).2.1 = some xs) :
    xs.length = 4 ∧ ∀ a ∈ xs, a < 2147483647 :=
  ⟨accepted_limbs_length H 4 _ xs h,accepted_limbs_canonical H 4 _ xs h⟩

#print axioms accepted_limbs_length
#print axioms accepted_limbs_canonical
#print axioms challenge_four_canonical_limbs
end AspisV8R19.QM31SamplerInvariants
