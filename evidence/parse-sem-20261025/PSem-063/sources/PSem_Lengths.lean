import PSem_Expansion
set_option autoImplicit false
namespace AspisR1.PSem_Lengths
open AspisV8R19.DuplexFrames OraclePortCompactDraft

theorem size_mod (row : Nat) : (rowShape row).2 % 32=0 := by
  unfold rowShape
  split_ifs <;> decide

theorem row_length (row : Nat) (b : Bytes)
    (bound : 5+(if 14 ≤ row then (rowShape row).2/2 else (rowShape row).2) ≤ b.length) :
    (PSem_Rows.expandedRow row b).length=5+(rowShape row).2 := by
  have mod := size_mod row
  have header : (b.take 5).length=5 := by rw [List.length_take,Nat.min_eq_left (by omega)]
  by_cases compact : 14 ≤ row
  · have payload : (slice b 5 ((rowShape row).2/2)).length=16*((rowShape row).2/32) := by
      simp only [slice,List.length_take,List.length_drop]
      simp only [if_pos compact] at bound
      omega
    simp only [PSem_Rows.expandedRow,if_pos compact,List.length_append,header]
    rw [PSem_Expand.expand_length _ _ payload]
    omega
  · simp only [if_neg compact] at bound
    simp only [PSem_Rows.expandedRow,if_neg compact,List.length_append,header,
      slice,List.length_take,List.length_drop]
    omega

inductive Rows : Nat → List Bytes → Prop where
  | nil (row : Nat) : Rows row []
  | cons {row : Nat} {b : Bytes} {bs : List Bytes}
      (size : b.length=5+(rowShape row).2) (tail : Rows (row+1) bs) : Rows row (b::bs)

theorem expanded_lengths (fuel row : Nat) (b : Bytes) (rs : List Bytes)
    (parsed : PSem_Rows.expandRows fuel row b=some rs) : Rows row rs := by
  induction fuel generalizing row b rs with
  | zero =>
    simp only [PSem_Rows.expandRows] at parsed
    split at parsed
    · cases parsed; exact .nil _
    · cases parsed
  | succ fuel ih =>
    by_cases compact : 14 ≤ row
    all_goals
      simp only [PSem_Rows.expandRows,compact,reduceIte] at parsed
      split at parsed
      · cases parsed
      · rename_i enough
        simp only [Bind.bind,Pure.pure,Option.bind_eq_some_iff,Option.some.injEq] at parsed
        obtain ⟨tail,ht,he⟩ := parsed
        cases he
        apply Rows.cons
        · apply row_length
          simpa only [compact,reduceIte] using Nat.le_of_not_gt enough
        · exact ih _ _ _ ht

theorem flatten_injective (row : Nat) (xs ys : List Bytes)
    (hx : Rows row xs) (hy : Rows row ys) (same : xs.flatten=ys.flatten) : xs=ys := by
  induction hx generalizing ys with
  | nil row =>
    cases hy with
    | nil => rfl
    | cons size tail =>
      have lengths := congrArg List.length same
      simp only [List.flatten_nil,List.flatten_cons,List.length_append,List.length_nil] at lengths
      omega
  | @cons row b bs size tail ih =>
    cases hy with
    | nil =>
      have lengths := congrArg List.length same
      simp only [List.flatten_nil,List.flatten_cons,List.length_append,List.length_nil] at lengths
      omega
    | @cons _ c cs size2 tail2 =>
      have equalLength : b.length=c.length := size.trans size2.symm
      simp only [List.flatten_cons] at same
      have front := congrArg (fun zs : Bytes => zs.take b.length) same
      simp only [List.take_left,equalLength] at front
      have rest := congrArg (fun zs : Bytes => zs.drop b.length) same
      simp only [List.drop_left,equalLength] at rest
      exact congrArg₂ List.cons front (ih cs tail2 rest)

#print axioms size_mod
#print axioms row_length
#print axioms expanded_lengths
#print axioms flatten_injective
end AspisR1.PSem_Lengths
