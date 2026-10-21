import OraclePortCandidateChecksC4
import OraclePortSelectedArithmeticC4

/-! Selected recovery is insufficient for equality of word-carrying rows.
This counterexample is to that proposed inference, not an accepted-run
counterexample. Collision exclusion authenticates selected leaves; it does
not require the prover to have read only those leaves before commitment. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.OraclePortSelectedRowObstructionC5
open AspisV8R19.DuplexFrames
open CanonicalCutEnrichedTranscript

/-- Change only a final-word coordinate outside the first four-entry fibre. -/
def alter (w : Words) : Words :=
  {w with final := fun i => if i.val = 4 then w.final i + 1 else w.final i}

theorem selected_same (w : Words) (i : Fin 262144) (hi : i.val < 4) :
    (alter w).c1 = w.c1 ∧ (alter w).c2 = w.c2 ∧ (alter w).final i = w.final i := by
  exact ⟨rfl,rfl,by simp only [alter,if_neg (show i.val ≠ 4 by omega)]⟩

theorem final_different (w : Words) : (alter w).final ≠ w.final := by
  intro same
  have h := congrFun same ⟨4,by decide⟩
  change w.final ⟨4,by decide⟩ + 1 = w.final ⟨4,by decide⟩ at h
  have bad : (1 : LiteralTranscript.E) = 0 := add_left_cancel (h.trans (add_zero _).symm)
  exact one_ne_zero bad

/-- Even the exact erased row and all selected metadata can agree while the
literal message differs, because `.second` stores the whole final word. -/
theorem row_different (w : Words) (payload : LiteralTranscript.BytesMessage) :
    LiteralTranscript.erase (LiteralTranscript.Message.second payload (alter w).final) =
      LiteralTranscript.erase (.second payload w.final) ∧
    LiteralTranscript.Message.second payload (alter w).final ≠ .second payload w.final := by
  refine ⟨rfl,?_⟩
  intro same
  exact final_different w (LiteralTranscript.Message.second.inj same).2

/-- There is an unselected final-word coordinate even for distinct queries.
The proof uses only cardinality transport over 22 × 4, never enumerates the
262144-element word domain. -/
theorem unselected_exists (q : Fin 22 → Fin 262144) :
    ∃ i : Fin 262144, ∀ j : Fin 22, ∀ slot : Fin 4,
      i ≠ childIndex (n := 65536) (parentIndex (n := 65536) (q j)) slot := by
  let route : Fin 22 × Fin 4 → Fin 262144 := fun js =>
    childIndex (n := 65536) (parentIndex (n := 65536) (q js.1)) js.2
  have small : (Finset.univ.image route).card ≤ 88 := by
    exact (Finset.card_image_le).trans (by simp)
  by_contra no
  push_neg at no
  have all : Finset.univ ⊆ Finset.univ.image route := by
    intro i _
    obtain ⟨j,slot,eq⟩ := no i
    exact Finset.mem_image.mpr ⟨(j,slot),Finset.mem_univ _,eq.symm⟩
  have large := Finset.card_le_card all
  have size : (Finset.univ : Finset (Fin 262144)).card = 262144 := by
    exact Fintype.card_fin _
  rw [size] at large
  omega

/-- Exact selected folded-fibre agreement cannot imply full-word equality.
No accepted-execution existence is asserted by this countermodel. -/
theorem selected_fibres_do_not_determine_rows (q : Fin 22 → Fin 262144)
    (w : Words) : ∃ other : Words,
      other.c1 = w.c1 ∧ other.c2 = w.c2 ∧
      (∀ j : Fin 22, ∀ slot : Fin 4,
        other.final (childIndex (n := 65536) (parentIndex (n := 65536) (q j)) slot) =
          w.final (childIndex (n := 65536) (parentIndex (n := 65536) (q j)) slot)) ∧
      other.final ≠ w.final := by
  obtain ⟨i,missing⟩ := unselected_exists q
  let other : Words := {w with final := fun k => if k = i then w.final k + 1 else w.final k}
  refine ⟨other,rfl,rfl,?_,?_⟩
  · intro j slot
    exact if_neg (Ne.symm (missing j slot))
  · intro eq
    have h := congrFun eq i
    change (if i = i then w.final i + 1 else w.final i) = w.final i at h
    rw [if_pos rfl] at h
    exact one_ne_zero (add_left_cancel (h.trans (add_zero _).symm))

#print axioms unselected_exists
#print axioms selected_fibres_do_not_determine_rows
#print axioms selected_same
#print axioms final_different
#print axioms row_different
end AspisR1.OraclePortSelectedRowObstructionC5
end
