import AspisV8R19.SamplerRawStateRepresentation
import AspisV8R19.QM31SamplerProgram

/-! Deterministic cursor/read correspondence for the raw-state bridge.

These lemmas expose only the value, trace, and cursor-state equalities of one
source read.  They make no statement about oracle freshness or distributions.
-/
set_option autoImplicit false
namespace AspisV8R19.SamplerRawCursorBridge

open DuplexFrames SourceDuplexStep SamplerWords
open AspisV8R19.QM31SamplerProgram
open AspisV8R19.SamplerRawStateRepresentation

theorem readRun_before_rollover (H : Bytes → State) (c : Cursor)
    (h : c.index.val < 8) :
    readRun H c =
      ([],
        ( ((stateRawEquiv c.block) ⟨c.index.val, h⟩).val,
          ⟨c.state, c.block,
            ⟨c.index.val + 1, by omega⟩⟩)) := by
  have hne : c.index.val ≠ 8 := by omega
  simp [readRun, hne, stateRawEquiv_word]

theorem readRun_rollover (H : Bytes → State) (c : Cursor)
    (h : c.index.val = 8) :
    readRun H c =
      (calls H c.state,
        ( ((stateRawEquiv (step H c.state).1) 0).val,
          ⟨(step H c.state).2, (step H c.state).1, ⟨1, by decide⟩⟩)) := by
  simp [readRun, h, stateRawEquiv_word]

theorem readRun_cases (H : Bytes → State) (c : Cursor) :
    (∃ h : c.index.val < 8, readRun H c =
      ([],
        ( ((stateRawEquiv c.block) ⟨c.index.val, h⟩).val,
          ⟨c.state, c.block, ⟨c.index.val + 1, by omega⟩⟩))) ∨
    c.index.val = 8 ∧ readRun H c =
      (calls H c.state,
        ( ((stateRawEquiv (step H c.state).1) 0).val,
          ⟨(step H c.state).2, (step H c.state).1, ⟨1, by decide⟩⟩)) := by
  by_cases h : c.index.val = 8
  · exact Or.inr ⟨h, readRun_rollover H c h⟩
  · left
    have hlt : c.index.val < 8 := by
      have hle := c.index.isLt
      omega
    exact ⟨hlt, readRun_before_rollover H c hlt⟩

#print axioms readRun_before_rollover
#print axioms readRun_rollover
#print axioms readRun_cases
end AspisV8R19.SamplerRawCursorBridge
