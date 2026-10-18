import PoseidonLeadingAbsorb
import PoseidonFullRoundLazyExact
import PoseidonFullRoundPackedExact
import PoseidonInitialConstantsExact

/-! The actual leading-pair source caller, composing absorption, the leading
external layer, the first full round, and the final packed full round. -/
set_option autoImplicit false
namespace AspisR1.PoseidonLeadingPairExact
open Aeneas Aeneas.Std Result
open AspisR1SelectedMaskProbe
open AspisR1.PoseidonFullRoundCellStep
open AspisR1.PoseidonExternalPackedGroupCall (Packed packedCell packedCanonical)
open AspisR1.ExtractedMaskQmPackBase4Arithmetic (iBasis uBasis)
open AspisR1.PoseidonExternalPackedModel (lane)
abbrev Openings := state_only_poseidon.StateOnlyPoseidonOpenings
abbrev decodedState := AspisR1.PoseidonFullRoundLazyExact.decodedState
abbrev decodedConstants := AspisR1.PoseidonFullRoundLazyExact.decodedConstants

theorem source_success (o : Openings)
    (hz : CanonicalState o.z) (habsorption : CanonicalState o.xor12_z) :
    ∃ out : Packed,
      state_only_poseidon.leading_pair_packed o = .ok out ∧
      packedCanonical out ∧ ∀ group : Fin 4, Decode (packedCell out group) =
        R0P.poseidonPackingFormula iBasis uBasis (fun j =>
          R0P.poseidonLeadingPair (decodedState o.z) (decodedState o.xor12_z) (lane group j)) := by
  obtain ⟨absorbed,habs,habsCan,habsModel⟩ :=
    AspisR1.PoseidonLeadingAbsorb.source_success o.xor12_z o.z habsorption hz
  obtain ⟨initial,hinitial,hinitialCan,hinitialModel⟩ :=
    AspisR1.PoseidonExternalLinearExact.external_linear_lazy_success absorbed habsCan
  let c0 := AspisR1.PoseidonInitialConstantsExact.row (⟨0,by decide⟩ : Fin 4)
  let c1 := AspisR1.PoseidonInitialConstantsExact.row (⟨1,by decide⟩ : Fin 4)
  have hc0 : Array.index_usize poseidon2.EXTERNAL_INITIAL 0#usize = .ok c0 :=
    AspisR1.PoseidonInitialConstantsExact.row_source_read 0#usize (by decide)
  have hc1 : Array.index_usize poseidon2.EXTERNAL_INITIAL 1#usize = .ok c1 :=
    AspisR1.PoseidonInitialConstantsExact.row_source_read 1#usize (by decide)
  obtain ⟨middle,hmiddle,hmiddleCan,hmiddleModel⟩ :=
    AspisR1.PoseidonFullRoundLazyExact.m31_source_success initial c0 hinitialCan
      (AspisR1.PoseidonInitialConstantsExact.row_canonical _)
  obtain ⟨out,hout,houtCan,houtModel⟩ :=
    AspisR1.PoseidonFullRoundPackedExact.m31_source_success middle c1 hmiddleCan
      (AspisR1.PoseidonInitialConstantsExact.row_canonical _)
  have hdecoded0 : decodedConstants c0 = R0P.poseidonExternalInitial (⟨0,by decide⟩ : Fin 4) := by
    funext j
    exact AspisR1.PoseidonInitialConstantsExact.row_model _ j
  have hdecoded1 : decodedConstants c1 = R0P.poseidonExternalInitial (⟨1,by decide⟩ : Fin 4) := by
    funext j
    exact AspisR1.PoseidonInitialConstantsExact.row_model _ j
  have habsorbed : decodedState absorbed = fun j =>
      if j.val < 8 then decodedState o.z j + decodedState o.xor12_z j
      else decodedState o.z j := by
    funext j
    exact habsModel j
  have hinitialDecoded : decodedState initial =
      R0P.poseidonExternalLinear (decodedState absorbed) := by
    funext j
    exact hinitialModel j
  have hmiddleDecoded : decodedState middle =
      R0P.poseidonFullRound (decodedState initial) (decodedConstants c0) := by
    funext j
    exact hmiddleModel j
  refine ⟨out,?_,houtCan,?_⟩
  · simp only [state_only_poseidon.leading_pair_packed,habs,bind_tc_ok,
      hinitial,hc0,hmiddle,hc1,hout]
  · intro group
    have hm := houtModel group
    change Decode (packedCell out group) =
      R0P.poseidonPackingFormula iBasis uBasis (fun j =>
        R0P.poseidonFullRound (decodedState middle) (decodedConstants c1) (lane group j)) at hm
    rw [hmiddleDecoded,hinitialDecoded,habsorbed,hdecoded0,hdecoded1] at hm
    have hzero : (⟨0, by decide⟩ : Fin 4) = (0 : Fin 4) := Fin.ext rfl
    have hone : (⟨1, by decide⟩ : Fin 4) = (1 : Fin 4) := Fin.ext rfl
    rw [hzero, hone] at hm
    simpa only [R0P.poseidonLeadingPair] using hm

#print axioms source_success
end AspisR1.PoseidonLeadingPairExact
