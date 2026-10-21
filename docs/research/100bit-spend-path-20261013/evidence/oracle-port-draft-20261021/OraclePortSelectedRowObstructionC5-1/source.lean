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
  change (if (4 : Nat) = 4 then w.final ⟨4,by decide⟩ + 1 else _) = _ at h
  rw [if_pos rfl] at h
  have bad : (1 : LiteralTranscript.E) = 0 := add_left_cancel (h.trans (add_zero _).symm)
  exact one_ne_zero bad

/-- Even the exact erased row and all selected metadata can agree while the
literal message differs, because `.second` stores the whole final word. -/
theorem row_different (w : Words) (payload : Bytes) :
    LiteralTranscript.erase (LiteralTranscript.Message.second payload (alter w).final) =
      LiteralTranscript.erase (.second payload w.final) ∧
    LiteralTranscript.Message.second payload (alter w).final ≠ .second payload w.final := by
  refine ⟨rfl,?_⟩
  intro same
  exact final_different w (LiteralTranscript.Message.second.inj same).2

#print axioms selected_same
#print axioms final_different
#print axioms row_different
end AspisR1.OraclePortSelectedRowObstructionC5
end
