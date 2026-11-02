import PV_B3P_SemanticCallees557227
import PV_B3P_HornerLoopBinding8227
namespace PV_B3P_Closure557227
open Aeneas Aeneas.Std PV_B3P_227 PV_B3P_Success227 Result ControlFlow Error
set_option autoImplicit false
noncomputable section
attribute [local irreducible] local_bodies557
/-- Same caller control/dataflow with the fixed bound local callees substituted.
Remaining unchanged helpers and std/source coverage are separate obligations. -/
def composition_callees557 : PV_B3P_Binding13227.CompositionFn13 :=
  fun public1 claims point lambda chi theta => do
  let (amount, invalid) ← match public1.withdrawal_amount with
    | none => .ok (none,false)
    | some value => do
      let bad : Bool ← if value = 0#u32 then .ok true else do
        let upper ← lift (U32.wrapping_shl 1#u32 30#u32)
        .ok (decide (value >= upper))
      .ok (public1.withdrawal_amount,bad)
  if invalid then
    .ok (.Err reference_terminal.PoolV1PairForestSemanticTerminalErrorV1.InvalidPublicAmount)
  else do
    let transition ← local_bodies557.body16 {public1 with withdrawal_amount := amount}
    let branch ← core.result.Result.Insts.CoreOpsTry.branch transition
    match branch with
    | .Continue _ => do
      let z ← reference_terminal.select_c1_227 claims 0#usize
      let succ ← reference_terminal.select_c1_227 claims 1#usize
      let xor12 ← reference_terminal.select_c1_227 claims 2#usize
      let mask ← reference_terminal.composition_parts_loop0 claims
        (Array.repeat 10#usize aspis_core.field.QM31.ZERO) 0#usize
      let selectors ← reference_copy_terminal.Selectors.boxed_at_point point
      let selected ← local_bodies557.body10 selectors
      let poseidon ← local_bodies557.body23
        { z, succ_z := succ, xor12_z := xor12 } selected
      let semantic ← semantic_callees557 {public1 with withdrawal_amount := amount}
        { z, succ_z := succ, xor12_z := xor12 } selectors
      let h1_column ← reference_terminal.SELECTED_H1_COLUMN
      let h1 ← reference_terminal.selected_claim claims 0#usize h1_column
      let variant ← reference_terminal.copy_variant public1.variant
      let copy ← reference_copy_terminal.evaluate_with_selectors z h1 selectors lambda chi
        public1.transition.live_snapshot.next_pair_index variant
      let prepared ← host_terminal_field.PreparedQm31Multiplier.new theta
      let semantic_slice ← lift (Array.to_slice semantic)
      let first ← horner_direct_loop8 semantic prepared copy.residual (Slice.len semantic_slice)
      let poseidon_slice ← lift (Array.to_slice poseidon)
      let final ← horner_direct_loop8 poseidon prepared first (Slice.len poseidon_slice)
      let g_column ← reference_terminal.SELECTED_G_COLUMN
      let g ← reference_terminal.selected_claim claims 0#usize g_column
      .ok (.Ok (final,z,mask,g,h1,copy.active))
    | .Break residual =>
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
        (aspis_core.field.QM31 × Array aspis_core.field.QM31 16#usize ×
          Array aspis_core.field.QM31 10#usize × aspis_core.field.QM31 ×
          aspis_core.field.QM31 × aspis_core.field.QM31)
        (core.convert.FromSame reference_terminal.PoolV1PairForestSemanticTerminalErrorV1) residual

theorem composition_callees_reference557 :
    composition_callees557 = reference_terminal.composition_parts := by
  have restored : composition_callees557 = PV_B3P_Association554227.composition_source554 := by
    unfold composition_callees557 PV_B3P_Association554227.composition_source554
    rw [local_links557.link16,local_links557.link10,local_links557.link23,
      semantic_callees_reference557]
  exact Eq.trans restored PV_B3P_Association554227.composition_source_link554

#print axioms composition_callees_reference557
end
end PV_B3P_Closure557227
