import Aeneas
namespace R1Z.PV_DL_EncoderPairs
set_option autoImplicit false

/-- Forward-only size-two chunk iterator. A consumed pair is removed from the
remaining input; no mixed front/back iterator model is used. -/
def chunks {E : Type} : List E → List (E×E)
  | a::b::tail => (a,b)::chunks tail
  | _ => []

theorem length {E : Type} (xs : List E) : (chunks xs).length=xs.length/2 := by
  cases xs with
  | nil => simp [chunks]
  | cons a xs =>
    cases xs with
    | nil => simp [chunks]
    | cons b tail =>
      have ih := length tail
      simp only [chunks,List.length_cons] at *
      omega
termination_by xs.length

theorem coordinate {E : Type} (i : Nat) (xs : List E) :
    (chunks xs)[i]?=(do let a ← xs[2*i]?;let b ← xs[2*i+1]?;some (a,b)) := by
  induction i generalizing xs with
  | zero =>
    cases xs with
    | nil => simp [chunks]
    | cons a xs => cases xs <;> rfl
  | succ i ih =>
    cases xs with
    | nil => simp [chunks]
    | cons a xs =>
      cases xs with
      | nil => simp [chunks]
      | cons b tail =>
        have he : 2*(i+1)=2*i+2 := by omega
        have ho : 2*(i+1)+1=2*i+3 := by omega
        simp only [chunks,List.getElem?_cons_succ,ih,he,ho]

theorem message_count {E : Type} (xs : List E) (h : xs.length=1024) :
    (chunks xs).length=512 := by rw [length,h]

#print axioms chunks
#print axioms length
#print axioms coordinate
#print axioms message_count
end R1Z.PV_DL_EncoderPairs
