import PoseidonExternalGroupUpdateCells
import AspisR1.PoseidonClosure2GroupRange
import Aeneas.Std.WP
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
namespace AspisR1.PoseidonExternalLoopGroupBody
open Aeneas Aeneas.Std Result WP
open AspisR1SelectedMaskProbe
abbrev State := Array field.QM31 16#usize
abbrev QM := field.QM31
abbrev Decode := AspisR1.ExtractedMaskQM31Exact.decode

theorem group_body_success (state : State) (group : Usize) (hg : group.val < 4) :
  ∃ out : State,
    (do
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
      let state2 ← Array.update state1 i q5
      let q6 ← state_only_poseidon.external_linear_lazy_row input 2#usize
      let state3 ← Array.update state2 i1 q6
      let q7 ← state_only_poseidon.external_linear_lazy_row input 3#usize
      Array.update state3 i2 q7) = .ok out ∧
    ∀ j : Fin 4,
      Decode (AspisR1.PoseidonExternalGroupUpdateCells.cellAt out (4 * group.val + j.val)) =
        R0P.poseidonMat4 (fun k => Decode (AspisR1.PoseidonGroupSliceModel.cell16 state ⟨group.val,hg⟩ k)) j := by
  obtain ⟨start, finish, hrange, hstart, hfinish, hbound⟩ :=
    AspisR1.PoseidonClosure2GroupRange.group_range_success group hg
  have hmul : (4#usize * group : Result Usize) = .ok start := by
    have hmax := Usize.cMax_bound_concrete.1
    have hspec : (4#usize * group : Result Usize) ⦃z => z.val = 4 * group.val⦄ := by
      apply UScalar.mul_spec
      scalar_tac
    obtain ⟨z,hz,hval⟩ := WP.spec_imp_exists hspec
    have hz' : z = start := by
      apply UScalar.eq_of_val_eq
      omega
    simpa [hz'] using hz
  have hstartBound : start.val < 16 := by rw [hstart]; omega
  have hadd1Spec : (start + 1#usize : Result Usize) ⦃z => z.val = start.val + 1⦄ := by
    apply UScalar.add_spec
    scalar_tac
  obtain ⟨i, hiRun, hiVal⟩ := WP.spec_imp_exists hadd1Spec
  have hadd2Spec : (start + 2#usize : Result Usize) ⦃z => z.val = start.val + 2⦄ := by
    apply UScalar.add_spec
    scalar_tac
  obtain ⟨i1, hi1Run, hi1Val⟩ := WP.spec_imp_exists hadd2Spec
  have hadd3Spec : (start + 3#usize : Result Usize) ⦃z => z.val = start.val + 3⦄ := by
    apply UScalar.add_spec
    scalar_tac
  obtain ⟨i2, hi2Run, hi2Val⟩ := WP.spec_imp_exists hadd3Spec
  have hidx0 : start.val = 4 * group.val := hstart
  have hidx1 : i.val = 4 * group.val + 1 := by rw [hiVal,hstart]
  have hidx2 : i1.val = 4 * group.val + 2 := by rw [hi1Val,hstart]
  have hidx3 : i2.val = 4 * group.val + 3 := by rw [hi2Val,hstart]
  have hiBound : i.val < 16 := by rw [hidx1]; omega
  have hi1Bound : i1.val < 16 := by rw [hidx2]; omega
  have hi2Bound : i2.val < 16 := by rw [hidx3]; omega
  let q0 := state.val[start.val]'(by simpa [state.property] using hstartBound)
  let q1 := state.val[i.val]'(by simpa [state.property] using hiBound)
  let q2 := state.val[i1.val]'(by simpa [state.property] using hi1Bound)
  let q3 := state.val[i2.val]'(by simpa [state.property] using hi2Bound)
  have hread0 : Array.index_usize state start = .ok q0 :=
    AspisR1.RawPoseidonExternalRowReads.array_index_usize_ok state start hstartBound
  have hread1 : Array.index_usize state i = .ok q1 :=
    AspisR1.RawPoseidonExternalRowReads.array_index_usize_ok state i hiBound
  have hread2 : Array.index_usize state i1 = .ok q2 :=
    AspisR1.RawPoseidonExternalRowReads.array_index_usize_ok state i1 hi1Bound
  have hread3 : Array.index_usize state i2 = .ok q3 :=
    AspisR1.RawPoseidonExternalRowReads.array_index_usize_ok state i2 hi2Bound
  obtain ⟨out, hupdate, hmodel⟩ :=
    AspisR1.PoseidonExternalGroupUpdateCells.group_step_cell_values
      state ⟨group.val,hg⟩ q0 q1 q2 q3 start i i1 i2
      hread0 hread1 hread2 hread3 hidx0 hidx1 hidx2 hidx3
      hstartBound hiBound hi1Bound hi2Bound
  have hupdate' :
      (do
        let input ← core.array.Array.map
          (BuiltinFnMut QM (Array Std.U32 4#usize))
          (Array.make 4#usize [q0,q1,q2,q3]) state_only_poseidon.extension_limbs
        let q4 ← state_only_poseidon.external_linear_lazy_row input 0#usize
        let state1 ← Array.update state start q4
        let q5 ← state_only_poseidon.external_linear_lazy_row input 1#usize
        let state2 ← state1.update i q5
        let q6 ← state_only_poseidon.external_linear_lazy_row input 2#usize
        let state3 ← state2.update i1 q6
        let q7 ← state_only_poseidon.external_linear_lazy_row input 3#usize
        Array.update state3 i2 q7) = .ok out := by
    simpa only [hread0, hread1, hread2, hread3, bind_tc_ok] using hupdate
  refine ⟨out,?_,hmodel⟩
  simp only [hmul, hread0, hiRun, hread1, hi1Run, hread2, hi2Run, hread3,
    hupdate', bind_tc_ok]

#print axioms group_body_success
end AspisR1.PoseidonExternalLoopGroupBody
