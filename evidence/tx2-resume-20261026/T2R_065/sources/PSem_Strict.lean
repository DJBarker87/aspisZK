import PSem_Validation
import PSem_Canonical
set_option autoImplicit false
namespace AspisR1.PSem_Strict
open AspisV8R19.DuplexFrames OraclePortCompactDraft
open PSem_Validation

theorem head_checks (row : Nat) (b : Bytes)
    (bound : 5+(if 14 ≤ row then (rowShape row).2/2 else (rowShape row).2) ≤ b.length)
    (checked : Logical row (PSem_Rows.expandedRow row b)) :
    b.take 5=(⟨(rowShape row).1%256,Nat.mod_lt _ (by decide)⟩ :: le32 (rowShape row).2) ∧
      (14 ≤ row → canonical (slice b 5 (if 14 ≤ row then (rowShape row).2/2 else (rowShape row).2))) := by
  have headerLength : (b.take 5).length=5 := by rw [List.length_take,Nat.min_eq_left (by omega)]
  have header : (PSem_Rows.expandedRow row b).take 5=b.take 5 := by
    unfold PSem_Rows.expandedRow
    rw [List.take_append_of_le_length (by rw [headerLength])]
    simp only [List.take_take,Nat.min_self]
  refine ⟨header.symm.trans checked.1,?_⟩
  intro compact
  have payload : (PSem_Rows.expandedRow row b).drop 5=
      expand ((rowShape row).2/32) (slice b 5 ((rowShape row).2/2)) := by
    simp only [PSem_Rows.expandedRow,if_pos compact,List.drop_append,headerLength,Nat.sub_self,
      List.drop_zero,List.drop_take,Nat.sub_self,List.take_zero,List.nil_append]
  have mod := PSem_Lengths.size_mod row
  have length : (slice b 5 ((rowShape row).2/2)).length=16*((rowShape row).2/32) := by
    simp only [if_pos compact] at bound
    simp only [slice,List.length_take,List.length_drop]
    omega
  have canonicalPayload := checked.2 compact
  rw [payload] at canonicalPayload
  simp only [if_pos compact]
  exact (PSem_Canonical.canonical_expansion _ _ length).mp canonicalPayload

theorem valid_rows (fuel row : Nat) (b : Bytes) (rs : List Bytes)
    (expanded : PSem_Rows.expandRows fuel row b=some rs) (checked : Checked row rs) :
    PSem_Rows.ValidRows fuel row b := by
  induction fuel generalizing row b rs with
  | zero =>
    simp only [PSem_Rows.expandRows] at expanded
    split at expanded
    · assumption
    · cases expanded
  | succ fuel ih =>
    by_cases compact : 14 ≤ row
    all_goals
      simp only [PSem_Rows.expandRows,compact,reduceIte] at expanded
      split at expanded
      · cases expanded
      · rename_i enough
        simp only [Bind.bind,Pure.pure,Option.bind_eq_some_iff,Option.some.injEq] at expanded
        obtain ⟨tail,ht,he⟩ := expanded
        cases he
        have bound : 5+(if 14 ≤ row then (rowShape row).2/2 else (rowShape row).2) ≤ b.length := by
          simpa only [compact,reduceIte] using Nat.le_of_not_gt enough
        have head := head_checks row b bound checked.1
        have tailValid := ih (row+1) _ tail ht checked.2
        refine ⟨bound,head.1,head.2,?_⟩
        simp only [rowShape,ite] at tailValid ⊢
        cases dec : Nat.decLe 14 row with
        | isFalse no =>
          first
          | exact False.elim (no compact)
          | simpa only [dec] using tailValid
        | isTrue yes =>
          first
          | exact False.elim (compact yes)
          | simpa only [dec] using tailValid

theorem semantic_rows (fuel row : Nat) (b : Bytes) (rs : List Bytes)
    (expanded : PSem_Rows.expandRows fuel row b=some rs) (checked : Checked row rs) :
    semanticRows fuel row b=some rs :=
  (PSem_Rows.strict_iff fuel row b rs).mpr ⟨valid_rows fuel row b rs expanded checked,expanded⟩

#print axioms head_checks
#print axioms valid_rows
#print axioms semantic_rows
end AspisR1.PSem_Strict
