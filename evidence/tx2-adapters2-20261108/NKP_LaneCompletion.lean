import NKP_LaneCarrier
set_option autoImplicit false
noncomputable section
namespace NKP_LaneCompletion
open Aeneas Aeneas.Std Result
open NKP_LaneCuts
abbrev Lane := NKF_LaneConstructor.Lane
abbrev PE := NKF_BoxModel.PE
attribute [local instance] Classical.propDecidable
/-- Frozen suffix after the frontier loop: propagate its error, then test
zero-index root equality, then construct the owned lane. `emptyRoot` is a
source constant parameter for this LOCAL lemma; an admitted op50 root must
instantiate the pinned V7 table rather than introduce a runtime outcome. -/
def finish (bump : U8) (master : Array U8 32#usize) (lane : U8)
 (next : U64) (root emptyRoot : Node)
 (loop : Reply × Frontier × List (Fin 20)) :
 core.result.Result Lane PE × List (Fin 20) :=
 match loop with
 | (.Err e,_,calls) => (.Err e,calls)
 | (.Ok _,state,calls) =>
   if next.val = 0 ∧ root ≠ emptyRoot then (.Err .InvalidAccountData,calls)
   else (.Ok (NKP_LaneCarrier.make bump master lane next root state),calls)

theorem loop_error (bump : U8) (master : Array U8 32#usize) (lane : U8)
 (next : U64) (root emptyRoot : Node) (state : Frontier)
 (calls : List (Fin 20)) (e : PE) :
 finish bump master lane next root emptyRoot (.Err e,state,calls) = (.Err e,calls) := rfl

theorem rejected_root (bump : U8) (master : Array U8 32#usize) (lane : U8)
 (next : U64) (root emptyRoot : Node) (state : Frontier)
 (calls : List (Fin 20)) (zero : next.val = 0) (different : root ≠ emptyRoot) :
 finish bump master lane next root emptyRoot (.Ok (),state,calls) =
 (.Err .InvalidAccountData,calls) := by
 have bad : next.val = 0 ∧ root ≠ emptyRoot := ⟨zero,different⟩
 simp only [finish,if_pos bad]

theorem constructed (bump : U8) (master : Array U8 32#usize) (lane : U8)
 (next : U64) (root emptyRoot : Node) (state : Frontier)
 (calls : List (Fin 20)) (valid : next.val ≠ 0 ∨ root = emptyRoot) :
 finish bump master lane next root emptyRoot (.Ok (),state,calls) =
 (.Ok (NKP_LaneCarrier.make bump master lane next root state),calls) := by
 have notBad : ¬ (next.val = 0 ∧ root ≠ emptyRoot) := by
  intro bad
  cases valid with
  | inl h => exact h bad.1
  | inr h => exact bad.2 h
 simp only [finish,if_neg notBad]

theorem log_frame (bump : U8) (master : Array U8 32#usize) (lane : U8)
 (next : U64) (root emptyRoot : Node)
 (loop : Reply × Frontier × List (Fin 20)) :
 (finish bump master lane next root emptyRoot loop).2 = loop.2.2 := by
 rcases loop with ⟨reply,state,calls⟩
 cases reply with
 | Err e => rfl
 | Ok u =>
   by_cases bad : next.val = 0 ∧ root ≠ emptyRoot
   · simp only [finish,if_pos bad]
   · simp only [finish,if_neg bad]

/-- The actual one-iteration cut, not a whole-loop endpoint premise, drives
finite induction and the canonical constructor suffix. This remains LOCAL
support until the header/root decoder/SAME-call input and full native producer
are associated with op50. No parent or security row is closed by this lemma. -/
theorem compose {F : Type} (empty : Fin 20 → Node)
 (occupied : Fin 20 → Bool) (raw : Fin 20 → core.result.Result Node F)
 (step : Frontier → Fin 20 → Reply × Frontier)
 (cuts : ∀ before level, IterationCut (empty level) (occupied level) before
   (step before level).2 level (raw level) (step before level).1)
 (levels : List (Fin 20)) (before : Frontier)
 (bump : U8) (master : Array U8 32#usize) (lane : U8)
 (next : U64) (root emptyRoot : Node) :
 finish bump master lane next root emptyRoot (NKP_LaneInduction.fold step levels before) =
 finish bump master lane next root emptyRoot (NKF_LaneTrace.run empty occupied raw levels before) := by
 rw [NKP_LaneInduction.compose empty occupied raw step cuts levels before]

#print axioms loop_error
#print axioms rejected_root
#print axioms constructed
#print axioms log_frame
#print axioms compose
end NKP_LaneCompletion
