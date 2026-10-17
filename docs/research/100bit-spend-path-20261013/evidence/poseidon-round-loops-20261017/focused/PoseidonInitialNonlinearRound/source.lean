import PoseidonFullRoundLoopModel
import PoseidonInitialConstantsExact

/-! Bind actual initial-table reads to all cells of either nonlinear source
loop. No constant table or successful nonlinear traversal is assumed. -/
set_option autoImplicit false
namespace AspisR1.PoseidonInitialNonlinearRound
open Aeneas Aeneas.Std Result
open AspisR1SelectedMaskProbe
open AspisR1.PoseidonFullRoundCellStep
open AspisR1.PoseidonFullRoundLoopSource
open AspisR1.PoseidonFullRoundLoopModel

theorem source_read_and_cells (packed : Bool) (state : State)
    (round : Usize) (hround : round.val < 4) (hstate : CanonicalState state) :
    ∃ (constants1 : Constants) (out : State),
      Array.index_usize poseidon2.EXTERNAL_INITIAL round = .ok constants1 ∧
      loop packed { start := 0#usize, «end» := poseidon2.POSEIDON2_WIDTH }
        state constants1 = .ok out ∧ CanonicalState out ∧
      ∀ lane : Fin 16, Decode (cell out lane) =
        R0P.poseidonPow5 (Decode (cell state lane) +
          R0P.poseidonExternalInitial ⟨round.val,hround⟩ lane) := by
  obtain ⟨constants1,hread,hconstants,hconstantsModel⟩ :=
    AspisR1.PoseidonInitialConstantsExact.source_read_canonical_model round hround
  obtain ⟨out,hrun,hcanonical,hmodel⟩ := all_cells_success packed state constants1 hstate hconstants
  refine ⟨constants1,out,hread,hrun,hcanonical,?_⟩
  intro lane
  have h := hmodel lane
  change Decode (cell out lane) = R0P.poseidonPow5
    (Decode (cell state lane) + ((cell constants1 lane).val : Exact)) at h
  exact h.trans (congrArg (fun c : Exact => R0P.poseidonPow5 (Decode (cell state lane) + c))
    (hconstantsModel lane))

#print axioms source_read_and_cells
end AspisR1.PoseidonInitialNonlinearRound
