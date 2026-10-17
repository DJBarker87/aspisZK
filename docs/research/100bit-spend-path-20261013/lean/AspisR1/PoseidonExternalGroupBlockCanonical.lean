import PoseidonExternalGroupBlockFrame
import PoseidonExternalLoopGroupBody
import PoseidonExternalLoopStep
import AspisR1.PoseidonExternalGroupCanonical
import AspisR1.PoseidonFullRoundCellStep
import AspisR1.PoseidonClosure2GroupRange
import Aeneas.Std.WP
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
namespace AspisR1.PoseidonExternalGroupBlockCanonical
open Aeneas Aeneas.Std Result WP
open AspisR1SelectedMaskProbe
open AspisR1.PoseidonGroupSliceModel
open AspisR1.PoseidonExternalGroupBlockFrame
open AspisR1.PoseidonExternalLoopGroupBody
open AspisR1.PoseidonExternalLoopStep
open AspisR1.PoseidonExternalGroupCanonical
open AspisR1.PoseidonFullRoundCellStep
abbrev State := Array field.QM31 16#usize
abbrev QM := field.QM31

theorem group_block_canonical (state : State) (group : Usize) (hg : group.val < 4)
    (hstate : CanonicalState state) :
    ∃ out : State, groupBlock state group = .ok out ∧ CanonicalState out := by
  obtain ⟨out,hblock,_⟩ := group_block_frame state group hg
  obtain ⟨start,finish,hrange,hstart,hfinish,hbound⟩ :=
    AspisR1.PoseidonClosure2GroupRange.group_range_success group hg
  have hmul : (4#usize * group : Result Usize) = .ok start := by
    have hspec : (4#usize * group : Result Usize) ⦃z => z.val = 4 * group.val⦄ := by
      apply UScalar.mul_spec
      scalar_tac
    obtain ⟨z,hz,hval⟩ := WP.spec_imp_exists hspec
    have hz' : z = start := by apply UScalar.eq_of_val_eq; omega
    simpa [hz'] using hz
  have hstartBound : start.val < 16 := by rw [hstart]; omega
  have hplus1Spec : (start + 1#usize : Result Usize) ⦃z => z.val = start.val + 1⦄ := by
    apply UScalar.add_spec; scalar_tac
  obtain ⟨i,hiRun,hiVal⟩ := WP.spec_imp_exists hplus1Spec
  have hplus2Spec : (start + 2#usize : Result Usize) ⦃z => z.val = start.val + 2⦄ := by
    apply UScalar.add_spec; scalar_tac
  obtain ⟨i1,hi1Run,hi1Val⟩ := WP.spec_imp_exists hplus2Spec
  have hplus3Spec : (start + 3#usize : Result Usize) ⦃z => z.val = start.val + 3⦄ := by
    apply UScalar.add_spec; scalar_tac
  obtain ⟨i2,hi2Run,hi2Val⟩ := WP.spec_imp_exists hplus3Spec
  have hidx0 : start.val = 4 * group.val := hstart
  have hidx1 : i.val = 4 * group.val + 1 := by rw [hiVal,hstart]
  have hidx2 : i1.val = 4 * group.val + 2 := by rw [hi1Val,hstart]
  have hidx3 : i2.val = 4 * group.val + 3 := by rw [hi2Val,hstart]
  have hi0 : start.val < 16 := hstartBound
  have hi1 : i.val < 16 := by rw [hidx1]; omega
  have hi2 : i1.val < 16 := by rw [hidx2]; omega
  have hi3 : i2.val < 16 := by rw [hidx3]; omega
  let q0 := state.val[start.val]'(by simpa [state.property] using hi0)
  let q1 := state.val[i.val]'(by simpa [state.property] using hi1)
  let q2 := state.val[i1.val]'(by simpa [state.property] using hi2)
  let q3 := state.val[i2.val]'(by simpa [state.property] using hi3)
  have hr0 : Array.index_usize state start = .ok q0 :=
    AspisR1.RawPoseidonExternalRowReads.array_index_usize_ok state start hi0
  have hr1 : Array.index_usize state i = .ok q1 :=
    AspisR1.RawPoseidonExternalRowReads.array_index_usize_ok state i hi1
  have hr2 : Array.index_usize state i1 = .ok q2 :=
    AspisR1.RawPoseidonExternalRowReads.array_index_usize_ok state i1 hi2
  have hr3 : Array.index_usize state i2 = .ok q3 :=
    AspisR1.RawPoseidonExternalRowReads.array_index_usize_ok state i2 hi3
  obtain ⟨s4,hrun,hcan⟩ :=
    AspisR1.PoseidonExternalGroupCanonical.group_step_after_reads_canonical
      state q0 q1 q2 q3 start i i1 i2 hr0 hr1 hr2 hr3 hi0 hi1 hi2 hi3 hstate
  have hbody := AspisR1.PoseidonExternalLoopGroupBody.group_body_success state group hg
  obtain ⟨sbody,hbodyRun,_⟩ := hbody
  have hblock' := hblock
  unfold groupBlock at hblock'
  simp only [hmul,hr0,hiRun,hr1,hi1Run,hr2,hi2Run,hr3,bind_tc_ok] at hblock'
  have hrun' := hrun
  simp only [hr0,hr1,hr2,hr3,bind_tc_ok] at hrun'
  have hout : out = s4 := Result.ok.inj (hblock'.symm.trans hrun')
  exact ⟨out,hblock,hout ▸ hcan⟩
#print axioms group_block_canonical
end AspisR1.PoseidonExternalGroupBlockCanonical
