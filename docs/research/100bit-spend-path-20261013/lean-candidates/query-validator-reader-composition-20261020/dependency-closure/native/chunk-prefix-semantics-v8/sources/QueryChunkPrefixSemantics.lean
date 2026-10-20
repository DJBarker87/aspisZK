namespace AspisR1.QueryValidatorChunkSemantics

def prefixHit [BEq α] (xs : List α) (needle : α) : Nat → Bool
  | 0 => false
  | n + 1 =>
      match xs with
      | [] => false
      | x :: tail => (x == needle) || prefixHit tail needle n

theorem prefixHit_eq_any_take [BEq α] (xs : List α) (needle : α) (n : Nat) :
    prefixHit xs needle n = (xs.take n).any (fun x => x == needle) := by
  induction n generalizing xs with
  | zero => simp [prefixHit]
  | succ n ih =>
      cases xs with
      | nil => simp [prefixHit]
      | cons x tail => simp [prefixHit, ih]

def eagerChunk8 [BEq α] (xs : Fin 8 → α) (needle : α) (count : Nat) : Bool :=
  ((decide (0 < count) && (xs ⟨0, by decide⟩ == needle)) ||
   (decide (1 < count) && (xs ⟨1, by decide⟩ == needle)) ||
   (decide (2 < count) && (xs ⟨2, by decide⟩ == needle)) ||
   (decide (3 < count) && (xs ⟨3, by decide⟩ == needle)) ||
   (decide (4 < count) && (xs ⟨4, by decide⟩ == needle)) ||
   (decide (5 < count) && (xs ⟨5, by decide⟩ == needle)) ||
   (decide (6 < count) && (xs ⟨6, by decide⟩ == needle)) ||
   (decide (7 < count) && (xs ⟨7, by decide⟩ == needle)))

theorem eagerChunk8_true_iff [BEq α] (xs : Fin 8 → α) (needle : α) (count : Nat) :
    eagerChunk8 xs needle count = true ↔
      ((0 < count ∧ ((xs ⟨0, by decide⟩ == needle) = true)) ∨
       (1 < count ∧ ((xs ⟨1, by decide⟩ == needle) = true)) ∨
       (2 < count ∧ ((xs ⟨2, by decide⟩ == needle) = true)) ∨
       (3 < count ∧ ((xs ⟨3, by decide⟩ == needle) = true)) ∨
       (4 < count ∧ ((xs ⟨4, by decide⟩ == needle) = true)) ∨
       (5 < count ∧ ((xs ⟨5, by decide⟩ == needle) = true)) ∨
       (6 < count ∧ ((xs ⟨6, by decide⟩ == needle) = true)) ∨
       (7 < count ∧ ((xs ⟨7, by decide⟩ == needle) = true))) := by
  simp [eagerChunk8, or_assoc]

end AspisR1.QueryValidatorChunkSemantics
