import OraclePortCompactDraft
set_option autoImplicit false
noncomputable section
namespace AspisR1.PSem_Rows
open AspisV8R19.DuplexFrames OraclePortCompactDraft
attribute [local instance] Classical.propDecidable

/-- One compact row, with the stored framing copied and the implied high
halves inserted. This operation deliberately does not validate framing. -/
def expandedRow (row : Nat) (b : Bytes) : Bytes :=
  let size := (rowShape row).2
  let stored := if 14 ≤ row then size / 2 else size
  b.take 5 ++ if 14 ≤ row then expand (size/32) (slice b 5 stored)
    else slice b 5 stored

/-- Byte-level expansion stage. Source association is a separate obligation. -/
def expandRows : Nat → Nat → Bytes → Option (List Bytes)
  | 0, _, b => if b = [] then some [] else none
  | fuel+1, row, b => do
      let size := (rowShape row).2
      let stored := if 14 ≤ row then size / 2 else size
      if b.length < 5+stored then none else do
        let tail ← expandRows fuel (row+1) (b.drop (5+stored))
        pure (expandedRow row b :: tail)

/-- Checks on stored rows corresponding to the later strict logical parser.
No assertion about Rust execution is hidden in this predicate. -/
def ValidRows : Nat → Nat → Bytes → Prop
  | 0, _, b => b = []
  | fuel+1, row, b =>
      let (tag,size) := rowShape row
      let stored := if 14 ≤ row then size/2 else size
      5+stored ≤ b.length ∧
      b.take 5 = (⟨tag%256,Nat.mod_lt _ (by decide)⟩ :: le32 size) ∧
      (14 ≤ row → canonical (slice b 5 stored)) ∧
      ValidRows fuel (row+1) (b.drop (5+stored))

theorem strict_iff (fuel row : Nat) (b : Bytes) (rs : List Bytes) :
    semanticRows fuel row b = some rs ↔
      ValidRows fuel row b ∧ expandRows fuel row b = some rs := by
  induction fuel generalizing row b rs with
  | zero => simp only [semanticRows,ValidRows,expandRows]; split <;> simp_all
  | succ fuel ih =>
    by_cases compact : 14 ≤ row
    all_goals
      by_cases short : b.length < 5+(if 14 ≤ row then (rowShape row).2/2 else (rowShape row).2)
      · simp [semanticRows, ValidRows, expandRows, compact] at short ⊢
        omega
      · by_cases framing : b.take 5 =
          (⟨(rowShape row).1%256,Nat.mod_lt _ (by decide)⟩ :: le32 (rowShape row).2)
        · by_cases canon : canonical (slice b 5
            (if 14 ≤ row then (rowShape row).2/2 else (rowShape row).2))
          all_goals
            simp only [compact, reduceIte] at short canon
            simp [semanticRows,ValidRows,expandRows,expandedRow,compact,short,framing,canon,
              Option.bind_eq_some_iff,ih]
        · simp only [compact, reduceIte] at short
          simp [semanticRows,ValidRows,expandRows,compact,short,framing]

theorem semanticRows_length (fuel row : Nat) (b : Bytes) (rs : List Bytes)
    (h : semanticRows fuel row b = some rs) : rs.length = fuel := by
  induction fuel generalizing row b rs with
  | zero =>
    simp only [semanticRows] at h
    split at h
    · cases h; rfl
    · cases h
  | succ fuel ih =>
    have expansion := ((strict_iff _ _ _ _).mp h).2
    by_cases compact : 14 ≤ row
    all_goals
      simp only [expandRows,compact,reduceIte] at expansion
      split at expansion
      · cases expansion
      · simp only [Bind.bind, Pure.pure, Option.bind_eq_some_iff,
          Option.some.injEq] at expansion
        obtain ⟨tail,ht,he⟩ := expansion
        cases he
        have strictTail := ((strict_iff _ _ _ _).mp h).1.2.2.2
        have parsedTail := (strict_iff _ _ _ _).mpr ⟨strictTail,ht⟩
        simpa only [List.length_cons] using congrArg Nat.succ (ih _ _ _ parsedTail)

#print axioms semanticRows_length
#print axioms strict_iff
end AspisR1.PSem_Rows
end
