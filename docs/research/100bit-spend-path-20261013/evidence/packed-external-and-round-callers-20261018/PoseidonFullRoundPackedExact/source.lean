import PoseidonExternalPackedSource
import PoseidonFullRoundLoopModel
import PoseidonQMFullRoundLoopModel

/-! Actual packed full-round callers: the nonlinear loop is derived from
canonical input and then the checked packed external layer is invoked.
The result remains a literal pack; no injectivity of packing is asserted. -/
set_option autoImplicit false
namespace AspisR1.PoseidonFullRoundPackedExact
open Aeneas Aeneas.Std Result
open AspisR1SelectedMaskProbe
open AspisR1.PoseidonFullRoundCellStep
open AspisR1.PoseidonExternalPackedGroupCall (Packed packedCell packedCanonical)
open AspisR1.ExtractedMaskQmPackBase4Arithmetic (iBasis uBasis)
open AspisR1.PoseidonExternalPackedModel (lane)

def decodedState (state : State) : Fin 16 → Exact := fun j => Decode (cell state j)
def decodedConstants (constants1 : Constants) : Fin 16 → Exact :=
  fun j => ((cell constants1 j).val : Exact)

theorem m31_source_success (state : State) (constants1 : Constants)
    (hstate : CanonicalState state) (hconstants : CanonicalConstants constants1) :
    ∃ out : Packed,
      state_only_poseidon.full_round_m31_constants_packed state constants1 = .ok out ∧
      packedCanonical out ∧ ∀ group : Fin 4, Decode (packedCell out group) =
        R0P.poseidonPackingFormula iBasis uBasis (fun j =>
          R0P.poseidonFullRound (decodedState state) (decodedConstants constants1) (lane group j)) := by
  obtain ⟨nonlinear,hnonlinear,hcan,hmodel⟩ :=
    AspisR1.PoseidonFullRoundLoopModel.all_cells_success true state constants1 hstate hconstants
  obtain ⟨out,hexternal,houtCan,houtModel⟩ :=
    AspisR1.PoseidonExternalPackedSource.external_linear_packed_source_success nonlinear hcan
  have hnonlinearModel : decodedState nonlinear =
      fun j => R0P.poseidonPow5 (decodedState state j + decodedConstants constants1 j) := by
    funext j
    exact hmodel j
  refine ⟨out,?_,houtCan,?_⟩
  · change state_only_poseidon.full_round_m31_constants_packed_loop
      { start := 0#usize, «end» := poseidon2.POSEIDON2_WIDTH } state constants1 =
      .ok nonlinear at hnonlinear
    simp only [state_only_poseidon.full_round_m31_constants_packed,hnonlinear,bind_tc_ok,hexternal]
  · intro group
    have hm := houtModel group 0
    change Decode (packedCell out group) = R0P.poseidonPackingFormula iBasis uBasis
      (fun j => R0P.poseidonExternalLinear (decodedState nonlinear) (lane group j)) at hm
    rw [hnonlinearModel] at hm
    exact hm

theorem qm_source_success (state constants1 : State)
    (hstate : CanonicalState state) (hconstants : CanonicalState constants1) :
    ∃ out : Packed,
      state_only_poseidon.full_round_packed state constants1 = .ok out ∧
      packedCanonical out ∧ ∀ group : Fin 4, Decode (packedCell out group) =
        R0P.poseidonPackingFormula iBasis uBasis (fun j =>
          R0P.poseidonFullRound (decodedState state) (decodedState constants1) (lane group j)) := by
  obtain ⟨nonlinear,hnonlinear,hcan,hmodel⟩ :=
    AspisR1.PoseidonQMFullRoundLoopModel.all_cells_success true state constants1 hstate hconstants
  obtain ⟨out,hexternal,houtCan,houtModel⟩ :=
    AspisR1.PoseidonExternalPackedSource.external_linear_packed_source_success nonlinear hcan
  have hnonlinearModel : decodedState nonlinear =
      fun j => R0P.poseidonPow5 (decodedState state j + decodedState constants1 j) := by
    funext j
    exact hmodel j
  refine ⟨out,?_,houtCan,?_⟩
  · change state_only_poseidon.full_round_packed_loop
      { start := 0#usize, «end» := poseidon2.POSEIDON2_WIDTH } state constants1 =
      .ok nonlinear at hnonlinear
    simp only [state_only_poseidon.full_round_packed,hnonlinear,bind_tc_ok,hexternal]
  · intro group
    have hm := houtModel group 0
    change Decode (packedCell out group) = R0P.poseidonPackingFormula iBasis uBasis
      (fun j => R0P.poseidonExternalLinear (decodedState nonlinear) (lane group j)) at hm
    rw [hnonlinearModel] at hm
    exact hm

#print axioms m31_source_success
#print axioms qm_source_success
end AspisR1.PoseidonFullRoundPackedExact
