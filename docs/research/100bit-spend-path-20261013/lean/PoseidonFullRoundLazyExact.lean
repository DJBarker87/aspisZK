import PoseidonExternalLinearExact
import PoseidonFullRoundLoopModel
import PoseidonQMFullRoundLoopModel

/-! Actual lazy full-round callers, composed from the checked nonlinear
loops and checked external-linear caller. No intermediate success equation
is assumed. Constants and nonlinear maps remain symbolic. -/
set_option autoImplicit false
namespace AspisR1.PoseidonFullRoundLazyExact
open Aeneas Aeneas.Std Result
open AspisR1SelectedMaskProbe
open AspisR1.PoseidonFullRoundCellStep

def decodedState (state : State) : Fin 16 → Exact := fun j => Decode (cell state j)
def decodedConstants (constants1 : Constants) : Fin 16 → Exact :=
  fun j => ((cell constants1 j).val : Exact)

theorem m31_source_success (state : State) (constants1 : Constants)
    (hstate : CanonicalState state) (hconstants : CanonicalConstants constants1) :
    ∃ out : State,
      state_only_poseidon.full_round_m31_constants state constants1 = .ok out ∧
      CanonicalState out ∧ ∀ j : Fin 16, Decode (cell out j) =
        R0P.poseidonFullRound (decodedState state) (decodedConstants constants1) j := by
  obtain ⟨nonlinear,hnonlinear,hcan,hmodel⟩ :=
    AspisR1.PoseidonFullRoundLoopModel.all_cells_success false state constants1 hstate hconstants
  obtain ⟨out,hexternal,houtCan,houtModel⟩ :=
    AspisR1.PoseidonExternalLinearExact.external_linear_lazy_success nonlinear hcan
  have hnonlinearModel : decodedState nonlinear =
      fun j => R0P.poseidonPow5 (decodedState state j + decodedConstants constants1 j) := by
    funext j
    exact hmodel j
  refine ⟨out,?_,houtCan,?_⟩
  · change state_only_poseidon.full_round_m31_constants_loop
      { start := 0#usize, «end» := poseidon2.POSEIDON2_WIDTH } state constants1 =
      .ok nonlinear at hnonlinear
    simp only [state_only_poseidon.full_round_m31_constants,hnonlinear,bind_tc_ok,hexternal]
  · intro j
    have hm := houtModel j
    change Decode (cell out j) = R0P.poseidonExternalLinear (decodedState nonlinear) j at hm
    rw [hnonlinearModel] at hm
    exact hm

theorem qm_source_success (state constants1 : State)
    (hstate : CanonicalState state) (hconstants : CanonicalState constants1) :
    ∃ out : State,
      state_only_poseidon.full_round state constants1 = .ok out ∧
      CanonicalState out ∧ ∀ j : Fin 16, Decode (cell out j) =
        R0P.poseidonFullRound (decodedState state) (decodedState constants1) j := by
  obtain ⟨nonlinear,hnonlinear,hcan,hmodel⟩ :=
    AspisR1.PoseidonQMFullRoundLoopModel.all_cells_success false state constants1 hstate hconstants
  obtain ⟨out,hexternal,houtCan,houtModel⟩ :=
    AspisR1.PoseidonExternalLinearExact.external_linear_lazy_success nonlinear hcan
  have hnonlinearModel : decodedState nonlinear =
      fun j => R0P.poseidonPow5 (decodedState state j + decodedState constants1 j) := by
    funext j
    exact hmodel j
  refine ⟨out,?_,houtCan,?_⟩
  · change state_only_poseidon.full_round_loop
      { start := 0#usize, «end» := poseidon2.POSEIDON2_WIDTH } state constants1 =
      .ok nonlinear at hnonlinear
    simp only [state_only_poseidon.full_round,hnonlinear,bind_tc_ok,hexternal]
  · intro j
    have hm := houtModel j
    change Decode (cell out j) = R0P.poseidonExternalLinear (decodedState nonlinear) j at hm
    rw [hnonlinearModel] at hm
    exact hm

#print axioms m31_source_success
#print axioms qm_source_success
end AspisR1.PoseidonFullRoundLazyExact
