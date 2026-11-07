import NMM_LaneScalarSource
set_option autoImplicit false
set_option pp.proofs false
noncomputable section
namespace NMM_LaneAcceptance
open Aeneas Aeneas.Std Result AspisR1 NKP_LaneCuts
attribute [local instance] Classical.propDecidable

def writeAll (nodes : Fin 20 → Node) : List (Fin 20) → Frontier → Frontier
 | [],before => before
 | level::rest,before => writeAll nodes rest (NJD_LaneStep.write before level (nodes level))

/-- This theorem consumes successful typed replies and source guards. It is a
model composition lemma; none of its hypotheses is asserted as a native root. -/
theorem accepted {F : Type} (empty : Fin 20 → Node)
 (occupied : Fin 20 → Bool) (raw : Fin 20 → core.result.Result Node F)
 (nodes : Fin 20 → Node) (levels : List (Fin 20)) (before : Frontier)
 (replies : ∀ level ∈ levels, raw level = .Ok (nodes level))
 (guards : ∀ level ∈ levels, occupied level = true ∨ nodes level = empty level) :
 NKF_LaneTrace.run empty occupied raw levels before =
 (.Ok (),writeAll nodes levels before,levels) := by
 induction levels generalizing before with
 | nil => rfl
 | cons level rest ih =>
  have reply := replies level (by simp)
  have guard := (NKF_LaneFactor.accepted_guard (empty level) (nodes level) (occupied level)).mpr
   (guards level (by simp))
  simp only [NKF_LaneTrace.run,reply,NKF_LaneFactor.success_step,guard,writeAll]
  rw [ih _ (fun l hl => replies l (by simp [hl])) (fun l hl => guards l (by simp [hl]))]

/-- Disjoint writes preserve each selected payload until its own occurrence. -/
theorem writeAll_frame (nodes : Fin 20 → Node) (levels : List (Fin 20))
 (before : Frontier) (selected : Fin 20) (outside : selected ∉ levels) :
 writeAll nodes levels before selected = before selected := by
 induction levels generalizing before with
 | nil => rfl
 | cons level rest ih =>
  have different : selected ≠ level := by intro eq; exact outside (by simp [eq])
  have away : selected ∉ rest := by intro h; exact outside (by simp [h])
  rw [writeAll,ih _ away,NJD_LaneStep.frame _ _ _ _ different]

theorem writeAll_selected (nodes : Fin 20 → Node) (levels : List (Fin 20))
 (before : Frontier) (selected : Fin 20) (unique : levels.Nodup) (present : selected ∈ levels) :
 writeAll nodes levels before selected = nodes selected := by
 induction levels generalizing before with
 | nil => simp at present
 | cons level rest ih =>
  by_cases eq : selected=level
  · subst selected
    have away : level ∉ rest := (List.nodup_cons.mp unique).1
    rw [writeAll,writeAll_frame nodes rest _ level away,NJD_LaneStep.written]
  · exact ih _ (List.nodup_cons.mp unique).2 ((List.mem_cons.mp present).resolve_left eq)

#print accepted
#print axioms accepted
#print writeAll_frame
#print axioms writeAll_frame
#print writeAll_selected
#print axioms writeAll_selected
end NMM_LaneAcceptance
