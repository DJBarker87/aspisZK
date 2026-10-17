import PoseidonExternalLoopGroupBody
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
namespace AspisR1.PoseidonExternalLoopStep
open Aeneas Aeneas.Std Result
open AspisR1SelectedMaskProbe
abbrev State := Array field.QM31 16#usize
abbrev QM := field.QM31
abbrev Decode := AspisR1.ExtractedMaskQM31Exact.decode

def groupBlock (state : State) (group : Usize) : Result State := do
  let start ← 4#usize * group
  let q ← Array.index_usize state start
  let i ← start + 1#usize
  let q1 ← Array.index_usize state i
  let i1 ← start + 2#usize
  let q2 ← Array.index_usize state i1
  let i2 ← start + 3#usize
  let q3 ← Array.index_usize state i2
  let input ← core.array.Array.map
    (BuiltinFnMut QM (Array Std.U32 4#usize))
    (Array.make 4#usize [q,q1,q2,q3]) state_only_poseidon.extension_limbs
  let q4 ← state_only_poseidon.external_linear_lazy_row input 0#usize
  let state1 ← Array.update state start q4
  let q5 ← state_only_poseidon.external_linear_lazy_row input 1#usize
  let state2 ← state1.update i q5
  let q6 ← state_only_poseidon.external_linear_lazy_row input 2#usize
  let state3 ← state2.update i1 q6
  let q7 ← state_only_poseidon.external_linear_lazy_row input 3#usize
  state3.update i2 q7

theorem loop0_step (state : State) (group : Usize) (hg : group.val < 4) :
  ∃ out : State, ∃ group1 : Usize,
    state_only_poseidon.external_linear_lazy_loop0 state group =
      (do let out ← groupBlock state group
          let group1 ← group + 1#usize
          state_only_poseidon.external_linear_lazy_loop0 out group1) ∧
    group1.val = group.val + 1 ∧
    ∀ j : Fin 4,
      Decode (AspisR1.PoseidonExternalGroupUpdateCells.cellAt out (4 * group.val + j.val)) =
        R0P.poseidonMat4
          (fun k => Decode (AspisR1.PoseidonGroupSliceModel.cell16 state ⟨group.val,hg⟩ k)) j := by
  obtain ⟨out,hbody,hmodel⟩ :=
    AspisR1.PoseidonExternalLoopGroupBody.group_body_success state group hg
  have hplusSpec : (group + 1#usize : Result Usize) ⦃z => z.val = group.val + 1⦄ := by
    apply UScalar.add_spec
    scalar_tac
  obtain ⟨group1,hplus,hgroup1⟩ := WP.spec_imp_exists hplusSpec
  refine ⟨out,group1,?_,hgroup1,hmodel⟩
  have hbody' : groupBlock state group = .ok out := by
    simpa only [groupBlock] using hbody
  have hcont :
      (do let out ← groupBlock state group
          let group1 ← group + 1#usize
          state_only_poseidon.external_linear_lazy_loop0 out group1) =
        state_only_poseidon.external_linear_lazy_loop0 out group1 := by
    simp only [hbody', hplus, bind_tc_ok]
  have hcontFlat := hcont
  simp only [groupBlock, bind_assoc_eq] at hcontFlat
  rw [state_only_poseidon.external_linear_lazy_loop0.eq_def]
  have hlt : group < 4#usize := by scalar_tac
  rw [if_pos hlt]
  conv_rhs => simp only [hbody', hplus, bind_tc_ok]
  exact hcontFlat

#print axioms loop0_step
end AspisR1.PoseidonExternalLoopStep
