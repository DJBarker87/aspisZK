import RPz7_PAln_SequenceRead
set_option autoImplicit false
noncomputable section
namespace AspisR1.PAln_SemanticLayout
open AspisV8R19.DuplexFrames OraclePortCompactDraft

def Frame (row : Nat) (frame : Bytes) : Prop :=
  ∃ payload : Bytes,
    payload.length=(if 14≤row then (rowShape row).2/2 else (rowShape row).2) ∧
    (14≤row → canonical payload) ∧
    frame=(⟨(rowShape row).1%256,Nat.mod_lt _ (by decide)⟩::le32 (rowShape row).2)++
      (if 14≤row then expand ((rowShape row).2/32) payload else payload)

inductive Frames : Nat → List Bytes → Prop where
  | nil (row : Nat) : Frames row []
  | cons {row : Nat} {frame : Bytes} {tail : List Bytes}
      (head : Frame row frame) (rest : Frames (row+1) tail) : Frames row (frame::tail)

theorem layout (fuel row : Nat) (b : Bytes) (rs : List Bytes)
    (parsed : semanticRows fuel row b=some rs) : Frames row rs := by
  obtain ⟨valid,expanded⟩ := (PSem_Rows.strict_iff fuel row b rs).mp parsed
  clear parsed
  induction fuel generalizing row b rs with
  | zero =>
    have empty : b=[] := valid
    simp [PSem_Rows.expandRows,empty] at expanded
    subst rs
    exact .nil row
  | succ fuel ih =>
    by_cases compact : 14≤row
    all_goals
      simp only [PSem_Rows.ValidRows,compact,reduceIte] at valid
      obtain ⟨enough,header,canon,tailvalid⟩ := valid
      simp only [PSem_Rows.expandRows,compact,reduceIte] at expanded
      split at expanded
      · omega
      · simp only [Bind.bind,Pure.pure,Option.bind_eq_some_iff,Option.some.injEq] at expanded
        obtain ⟨tail,tailparsed,same⟩ := expanded
        subst rs
        refine .cons ?_ (ih _ _ _ tailvalid tailparsed)
        unfold Frame
        refine ⟨slice b 5 (if 14≤row then (rowShape row).2/2 else (rowShape row).2),?_,?_,?_⟩
        · simp only [compact,reduceIte,slice,List.length_take,List.length_drop]
          omega
        · simpa only [compact,reduceIte] using canon
        · simp only [PSem_Rows.expandedRow,compact,reduceIte,header]

theorem at_index (row : Nat) (rs : List Bytes) (frames : Frames row rs)
    (j : Nat) (b : Bytes) (slot : rs[j]?=some b) : Frame (row+j) b := by
  induction frames generalizing j with
  | nil => simp at slot
  | @cons row first tail head rest ih =>
    cases j with
    | zero => simp only [List.getElem?_cons_zero,Option.some.injEq] at slot;subst b;simpa using head
    | succ j =>
      simp only [List.getElem?_cons_succ] at slot
      have result := ih j slot
      simpa only [Nat.add_assoc,Nat.add_comm 1 j] using result

#print axioms layout
#print axioms at_index
end AspisR1.PAln_SemanticLayout
end
