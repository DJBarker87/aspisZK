import R1SelectedPrefixRead

/-! Sequence dependent optional entries over a finite index type. The
definition is executable and the characterization is purely structural. -/
set_option autoImplicit false

namespace AspisR1.FinOptionSequence

/-- Collect one optional value at each dependent `Fin` index, stopping at the
first missing entry. -/
def sequence {n : Nat} (A : Fin n → Type)
    (f : ∀ i, Option (A i)) : Option (∀ i, A i) :=
  match n with
  | 0 => some (fun i => Fin.elim0 i)
  | n + 1 =>
      (f 0).bind fun head =>
        (sequence (fun i => A i.succ) (fun i => f i.succ)).map
          (fun tail => Fin.cases head tail)

theorem sequence_succ {n : Nat} (A : Fin (n + 1) → Type)
    (f : ∀ i, Option (A i)) :
    sequence A f =
      (f 0).bind fun head =>
        (sequence (fun i => A i.succ) (fun i => f i.succ)).map
          (fun tail => Fin.cases head tail) := rfl

theorem sequence_iff_aux : ∀ n, ∀ (A : Fin n → Type)
    (f : ∀ i, Option (A i)) (values : ∀ i, A i),
    sequence A f = some values ↔ ∀ i, f i = some (values i) := by
  intro n
  induction n with
  | zero =>
      intro A f values
      constructor
      · intro _ i
        exact Fin.elim0 i
      · intro _
        exact congrArg some (funext fun i => Fin.elim0 i)
  | succ n ih =>
      intro A f values
      constructor
      · intro hseq i
        rw [sequence_succ] at hseq
        rcases Option.bind_eq_some_iff.mp hseq with
          ⟨head, hhead, htailMap⟩
        rcases Option.map_eq_some_iff.mp htailMap with
          ⟨tail, htail, happly⟩
        have hheadValue : head = values 0 := by
          have h := congrFun happly 0
          simpa using h
        have htailValue (j : Fin n) : tail j = values j.succ := by
          have h := congrFun happly j.succ
          simpa using h
        refine Fin.cases ?_ (fun j => ?_) i
        · simpa [hheadValue] using hhead
        · have hpoint := (ih (fun j => A j.succ)
            (fun j => f j.succ) tail).mp htail j
          simpa [htailValue j] using hpoint
      · intro hvalues
        have hhead := hvalues 0
        have htailValues (j : Fin n) :
            f j.succ = some (values j.succ) := hvalues j.succ
        have htail := (ih (fun j => A j.succ)
          (fun j => f j.succ) (fun j => values j.succ)).mpr htailValues
        rw [sequence_succ, hhead, Option.bind_some, htail]
        have happly : Fin.cases (values 0) (fun j => values j.succ) = values := by
          funext i
          refine Fin.cases ?_ (fun j => ?_) i <;> rfl
        rw [happly]

/-- The sequence succeeds exactly when every indexed optional value succeeds
with the corresponding component. -/
theorem sequence_eq_some_iff {n : Nat} (A : Fin n → Type)
    (f : ∀ i, Option (A i)) (values : ∀ i, A i) :
    sequence A f = some values ↔ ∀ i, f i = some (values i) :=
  sequence_iff_aux n A f values

#print axioms sequence_eq_some_iff

end AspisR1.FinOptionSequence
