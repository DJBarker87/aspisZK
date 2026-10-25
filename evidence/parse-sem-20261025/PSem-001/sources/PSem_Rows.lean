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

theorem semanticRows_length (fuel row : Nat) (b : Bytes) (rs : List Bytes)
    (h : semanticRows fuel row b = some rs) : rs.length = fuel := by
  induction fuel generalizing row b rs with
  | zero =>
    simp only [semanticRows] at h
    split at h
    · cases h; rfl
    · cases h
  | succ fuel ih =>
    simp only [semanticRows] at h
    split at h
    · cases h
    · split at h
      · cases h
      · split at h
        · cases h
        · simp only [Bind.bind, Pure.pure, Option.bind_eq_some_iff,
            Option.some.injEq] at h
          obtain ⟨tail,ht,rfl⟩ := h
          simpa only [List.length_cons] using congrArg Nat.succ (ih _ _ _ ht)

/-- A strict frozen parse is exactly expansion plus all row checks. This is
an equivalence of byte parsers, not a new accepted-execution assumption. -/
theorem strict_iff (fuel row : Nat) (b : Bytes) (rs : List Bytes) :
    semanticRows fuel row b = some rs ↔
      ValidRows fuel row b ∧ expandRows fuel row b = some rs := by
  induction fuel generalizing row b rs with
  | zero => simp only [semanticRows,ValidRows,expandRows]; split <;> simp_all
  | succ fuel ih =>
    simp only [semanticRows,ValidRows,expandRows]
    split
    · rename_i short
      simp only [Option.none_bind, reduceCtorEq, false_iff]
      rintro ⟨h,_⟩
      omega
    · rename_i enough
      split
      · rename_i bad
        simp only [Option.none_bind, reduceCtorEq, false_iff]
        rintro ⟨h,_⟩
        exact bad h.2.1
      · rename_i framing
        split
        · rename_i bad
          simp only [Option.none_bind, reduceCtorEq, false_iff]
          rintro ⟨h,_⟩
          exact bad.2 (h.2.2.1 bad.1)
        · rename_i canonicality
          simp only [Bind.bind, Pure.pure, Option.bind_eq_some_iff, Option.some.injEq]
          constructor
          · rintro ⟨tail,ht,he⟩
            obtain ⟨valid,expanded⟩ := (ih _ _ _).mp ht
            refine ⟨⟨by omega,by simpa using framing,?_,valid⟩,tail,expanded,?_⟩
            · intro compact
              by_contra noncanonical
              exact canonicality ⟨compact,noncanonical⟩
            · exact he
          · rintro ⟨⟨_,_,_,valid⟩,tail,expanded,he⟩
            exact ⟨tail,(ih _ _ _).mpr ⟨valid,expanded⟩,he⟩

#print axioms semanticRows_length
#print axioms strict_iff
end AspisR1.PSem_Rows
end
