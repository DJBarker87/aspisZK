import PoseidonExternalLoopStep
import PoseidonExternalGroupUpdateCells
import PoseidonExternalGroupFrame
import AspisR1.PoseidonClosure2GroupRange
import Aeneas.Std.WP
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
namespace AspisR1.PoseidonExternalGroupBlockFrame
open Aeneas Aeneas.Std Result WP
open AspisR1SelectedMaskProbe
open AspisR1.PoseidonExternalLoopStep
open AspisR1.PoseidonExternalLinearGroupModel
open AspisR1.PoseidonExternalGroupUpdateCells
open AspisR1.PoseidonGroupSliceModel
abbrev State := Array field.QM31 16#usize
abbrev QM := field.QM31

theorem group_block_frame (state : State) (group : Usize) (hg : group.val < 4) :
  ∃ out : State, groupBlock state group = .ok out ∧
    ∀ j : Fin 16, (∀ r : Fin 4, j.val ≠ 4 * group.val + r.val) →
      cellAt out j.val = cellAt state j.val := by
  obtain ⟨out,hbody,hmodel⟩ :=
    AspisR1.PoseidonExternalLoopGroupBody.group_body_success state group hg
  obtain ⟨start, finish, hrange, hstart, hfinish, hbound⟩ :=
    AspisR1.PoseidonClosure2GroupRange.group_range_success group hg
  have hmul : (4#usize * group : Result Usize) = .ok start := by
    have hspec : (4#usize * group : Result Usize) ⦃z => z.val = 4 * group.val⦄ := by
      apply UScalar.mul_spec
      scalar_tac
    obtain ⟨z,hz,hval⟩ := WP.spec_imp_exists hspec
    have hz' : z = start := by apply UScalar.eq_of_val_eq; omega
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
  obtain ⟨v0,v1,v2,v3,s1,s2,s3,s4,hrun,hs1,hs2,hs3,hs4,_⟩ :=
    AspisR1.PoseidonExternalLinearGroupModel.group_step_model
      state ⟨group.val,hg⟩ q0 q1 q2 q3 start i i1 i2
      hread0 hread1 hread2 hread3 hidx0 hidx1 hidx2 hidx3
      hstartBound hiBound hi1Bound hi2Bound
  have hblock : groupBlock state group = .ok out := by
    simpa only [groupBlock] using hbody
  have hblock' := hblock
  unfold groupBlock at hblock'
  simp only [hmul, hread0, hiRun, hread1, hi1Run, hread2, hi2Run, hread3,
    bind_tc_ok] at hblock'
  have hrun' := hrun
  simp only [hread0, hread1, hread2, hread3, bind_tc_ok] at hrun'
  have hout : out = s4 := Result.ok.inj (hblock'.symm.trans hrun')
  refine ⟨out, hblock, ?_⟩
  intro j hj
  subst out
  exact AspisR1.PoseidonExternalGroupFrame.four_updates_frame
    state s1 s2 s3 s4 ⟨group.val,hg⟩
    v0 v1 v2 v3 start i i1 i2 hs1 hs2 hs3 hs4
    hidx0 hidx1 hidx2 hidx3 hstartBound hiBound hi1Bound hi2Bound j hj

#print axioms group_block_frame
end AspisR1.PoseidonExternalGroupBlockFrame
