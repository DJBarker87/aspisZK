import PoseidonPreparedChannelLoopStep
import AspisR1PoseidonPreparedChannelRunStepLocal
import AspisR1PoseidonPreparedChannelNestedSet
import OccupancyRangeTraversal

set_option autoImplicit false
namespace AspisR1PoseidonPreparedChannelLoopExact
open Aeneas Aeneas.Std Result
open AspisR1SelectedMaskProbe

abbrev U64 := UScalar UScalarTy.U64
abbrev P : Nat := 2147483647
abbrev Sums := Array (Array U64 3#usize) 3#usize
abbrev PreparedArray := Array field.PreparedQm31Multiplier 3#usize
abbrev ComponentArray := Array (Array field.M31 3#usize) 3#usize
abbrev Range := core.ops.range.Range Std.Usize
abbrev Loop := AspisR1PoseidonPreparedSum3Source.field.qm31_sum_products3_prepared_loop0_loop0_loop0
open AspisR1PoseidonPreparedChannelRunStepLocal
open AspisR1PoseidonPreparedChannelNestedSet

private def leftCell (left : PreparedArray) (index component channel : Std.Usize)
    (hi : index.val < 3) (hc : component.val < 3) (hch : channel.val < 3) : field.M31 :=
  at3 (at3 (at3 left index hi).components component hc) channel hch

private def rightCell (right : ComponentArray) (component channel : Std.Usize)
    (hc : component.val < 3) (hch : channel.val < 3) : field.M31 :=
  at3 (at3 right component hc) channel hch

private def sumCell (sums : Sums) (component channel : Std.Usize)
    (hc : component.val < 3) (hch : channel.val < 3) : U64 :=
  at3 (at3 sums component hc) channel hch

/-- Exact execution of the actual innermost three-channel qmsum loop. A
processed channel receives one checked prepared-product accumulation; later
channels retain their previous outer-prefix sums. -/
theorem loop_success_fuel
    (left : PreparedArray) (right : ComponentArray) (index component : Std.Usize)
    (initial sums : Sums) (iter : Range) (fuel : Nat)
    (hindex : index.val < 3) (hcomponent : component.val < 3)
    (hend : iter.end.val = 3) (hspan : iter.start.val + fuel = 3)
    (hleft : ∀ ch (hch : ch.val < 3), (leftCell left index component ch hindex hcomponent hch).val < P)
    (hright : ∀ ch (hch : ch.val < 3), (rightCell right component ch hcomponent hch).val < P)
    (hbaseBound : ∀ ch (hch : ch.val < 3),
      (sumCell initial component ch hcomponent hch).val ≤ 2 * (P - 1) ^ 2)
    (hprocessed : ∀ ch (hch : ch.val < 3), ch.val < iter.start.val →
      (sumCell sums component ch hcomponent hch).val =
        (sumCell initial component ch hcomponent hch).val +
          (leftCell left index component ch hindex hcomponent hch).val *
            (rightCell right component ch hcomponent hch).val)
    (hremaining : ∀ ch (hch : ch.val < 3), iter.start.val ≤ ch.val →
      sumCell sums component ch hcomponent hch = sumCell initial component ch hcomponent hch)
    (hframe : ∀ c (hc : c.val < 3), c.val ≠ component.val →
      ∀ ch (hch : ch.val < 3),
        sumCell sums c ch hc hch = sumCell initial c ch hc hch) :
    ∃ out : Sums,
      Loop iter left sums index right component = .ok out ∧
      (∀ ch (hch : ch.val < 3),
        (sumCell out component ch hcomponent hch).val =
          (sumCell initial component ch hcomponent hch).val +
            (leftCell left index component ch hindex hcomponent hch).val *
              (rightCell right component ch hcomponent hch).val) ∧
      (∀ c (hc : c.val < 3), c.val ≠ component.val →
        ∀ ch (hch : ch.val < 3),
          sumCell out c ch hc hch = sumCell initial c ch hc hch) := by
  induction fuel generalizing iter sums with
  | zero =>
      have hstop : iter.start.val ≥ iter.end.val := by omega
      have hnext := AspisR1.OccupancyRangeTraversal.next_done iter hstop
      have hstart : iter.start.val = 3 := by omega
      refine ⟨sums, ?_, ?_, ?_⟩
      · change Loop iter left sums index right component = .ok sums
        rw [AspisR1PoseidonPreparedChannelLoopStep.generated_loop_step]
        simp only [hnext, bind_tc_ok]
      · intro ch hch
        exact hprocessed ch hch (by omega)
      · exact hframe
  | succ fuel ih =>
      have hlt : iter.start.val < iter.end.val := by omega
      have hchannelBound : iter.start.val < 3 := by omega
      obtain ⟨iter1, hnext, hstart1, hend1, _⟩ :=
        AspisR1.OccupancyRangeTraversal.next_step iter hlt
      have hend1' : iter1.end.val = 3 := by rw [hend1, hend]
      have hspan1 : iter1.start.val + fuel = 3 := by omega
      let channel := iter.start
      have hchannel : channel.val < 3 := by simpa [channel] using hchannelBound
      have hchannelStart : channel.val = iter.start.val := rfl
      have hcurrentRemaining := hremaining channel hchannel (by simp [channel])
      have hcurrentBound : (sumCell sums component channel hcomponent hchannel).val ≤
          2 * (P - 1) ^ 2 := by
        rw [hcurrentRemaining]
        exact hbaseBound channel hchannel
      obtain ⟨updated, sums1, hupd, hstep, hupdatedValue, hout⟩ :=
        AspisR1PoseidonPreparedChannelRunStepLocal.runStep_success
          left sums index right component channel hindex hcomponent hchannel
          (hleft channel hchannel) (hright channel hchannel) hcurrentBound
      have hprocessed1 : ∀ ch (hch : ch.val < 3), ch.val < iter1.start.val →
          (sumCell sums1 component ch hcomponent hch).val =
            (sumCell initial component ch hcomponent hch).val +
              (leftCell left index component ch hindex hcomponent hch).val *
                (rightCell right component ch hcomponent hch).val := by
        intro ch hch hj
        by_cases heq : ch.val = channel.val
        · have hcell : sumCell sums1 component ch hcomponent hch = updated := by
            rw [hout]
            have hnest := AspisR1PoseidonPreparedChannelNestedSet.cell_nested_set
              sums component channel ch ch (at3 sums component hcomponent) updated
              hcomponent hchannel hch hch rfl
            have hnest' := hnest
            rw [if_pos heq] at hnest'
            rw [if_pos (by rfl : ch.val = ch.val)] at hnest'
            simpa [sumCell] using hnest'
          rw [hcell, hupdatedValue, hcurrentRemaining] at *
          simpa [sumCell, leftCell, rightCell, channel] using hupdatedValue
        · have hjOld : ch.val < iter.start.val := by rw [hstart1] at hj; simp [channel] at heq; omega
          have hcell : sumCell sums1 component ch hcomponent hch = sumCell sums component ch hcomponent hch := by
            rw [hout]
            have hnest := AspisR1PoseidonPreparedChannelNestedSet.cell_nested_set
              sums component channel ch ch (at3 sums component hcomponent) updated
              hcomponent hchannel hch hch rfl
            have hneq : ch.val ≠ component.val := by
              intro hc
              apply heq
              simpa [channel] using hc
            simpa [sumCell, hneq, heq] using hnest
          rw [hcell]
          exact hprocessed ch hch hjOld
      have hremaining1 : ∀ ch (hch : ch.val < 3), iter1.start.val ≤ ch.val →
          sumCell sums1 component ch hcomponent hch = sumCell initial component ch hcomponent hch := by
        intro ch hch hj
        have hne : ch.val ≠ channel.val := by
          intro heq
          rw [hstart1, channel, hchannelStart] at hj
          omega
        rw [hout]
        have hnest := AspisR1PoseidonPreparedChannelNestedSet.cell_nested_set
          sums component channel ch ch (at3 sums component hcomponent) updated
          hcomponent hchannel hch hch rfl
        have hneq : ch.val ≠ component.val := by
          intro heq
          apply hne
          simpa [channel] using heq.symm
        simpa [sumCell, hneq, hne] using hnest.trans (hremaining ch hch (by omega))
      have hframe1 : ∀ c (hc : c.val < 3), c.val ≠ component.val →
          ∀ ch (hch : ch.val < 3),
            sumCell sums1 c ch hc hch = sumCell initial c ch hc hch := by
        intro c hc hne ch hch
        rw [hout]
        have hnest := AspisR1PoseidonPreparedChannelNestedSet.cell_nested_set
          sums component channel c ch (at3 sums component hcomponent) updated
          hcomponent hchannel hc hch rfl
        simpa [sumCell, hne] using hnest.trans (hframe c hc hne ch hch)
      obtain ⟨out, hrec, hformula, hframeOut⟩ :=
        ih iter1 sums1 hend1' hspan1 hleft hright hbaseBound hprocessed1 hremaining1 hframe1
      refine ⟨out, ?_, hformula, hframeOut⟩
      rw [AspisR1PoseidonPreparedChannelLoopStep.generated_loop_step]
      simp only [hnext, bind_tc_ok, hstep, hrec]

#print axioms loop_success_fuel
end AspisR1PoseidonPreparedChannelLoopExact
