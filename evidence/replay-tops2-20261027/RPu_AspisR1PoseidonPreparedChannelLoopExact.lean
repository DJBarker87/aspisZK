import RPu_PoseidonPreparedChannelLoopStep
import RPu_AspisR1PoseidonPreparedChannelRunStepLocal
import RPu_AspisR1PoseidonPreparedChannelNestedSet
import RPu_AspisR1PoseidonPreparedChannelUpdateInvariantV2
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

/-- Exact execution of the actual innermost three-channel qmsum loop. A
processed channel receives one checked prepared-product accumulation; later
channels retain their previous outer-prefix sums. -/
theorem loop_success_fuel
    (left : PreparedArray) (right : ComponentArray) (index component : Std.Usize)
    (initial sums : Sums) (iter : Range) (fuel : Nat)
    (hindex : index.val < 3) (hcomponent : component.val < 3)
    (hend : iter.end.val = 3) (hspan : iter.start.val + fuel = 3)
    (hleft : ∀ (ch : Std.Usize) (hch : ch.val < 3), (leftCell left index component ch hindex hcomponent hch).val < P)
    (hright : ∀ (ch : Std.Usize) (hch : ch.val < 3), (rightCell right component ch hcomponent hch).val < P)
    (hbaseBound : ∀ (ch : Std.Usize) (hch : ch.val < 3),
      (AspisR1PoseidonPreparedChannelUpdateInvariantV2.sumCell initial component ch hcomponent hch).val ≤ 2 * (P - 1) ^ 2)
    (hprocessed : ∀ (ch : Std.Usize) (hch : ch.val < 3), ch.val < iter.start.val →
      (AspisR1PoseidonPreparedChannelUpdateInvariantV2.sumCell sums component ch hcomponent hch).val =
        (AspisR1PoseidonPreparedChannelUpdateInvariantV2.sumCell initial component ch hcomponent hch).val +
          (leftCell left index component ch hindex hcomponent hch).val *
            (rightCell right component ch hcomponent hch).val)
    (hremaining : ∀ (ch : Std.Usize) (hch : ch.val < 3), iter.start.val ≤ ch.val →
      AspisR1PoseidonPreparedChannelUpdateInvariantV2.sumCell sums component ch hcomponent hch = AspisR1PoseidonPreparedChannelUpdateInvariantV2.sumCell initial component ch hcomponent hch)
    (hframe : ∀ (c : Std.Usize) (hc : c.val < 3), c.val ≠ component.val →
      ∀ (ch : Std.Usize) (hch : ch.val < 3),
        AspisR1PoseidonPreparedChannelUpdateInvariantV2.sumCell sums c ch hc hch = AspisR1PoseidonPreparedChannelUpdateInvariantV2.sumCell initial c ch hc hch) :
    ∃ out : Sums,
      Loop iter left sums index right component = .ok out ∧
      (∀ (ch : Std.Usize) (hch : ch.val < 3),
        (AspisR1PoseidonPreparedChannelUpdateInvariantV2.sumCell out component ch hcomponent hch).val =
          (AspisR1PoseidonPreparedChannelUpdateInvariantV2.sumCell initial component ch hcomponent hch).val +
            (leftCell left index component ch hindex hcomponent hch).val *
              (rightCell right component ch hcomponent hch).val) ∧
      (∀ (c : Std.Usize) (hc : c.val < 3), c.val ≠ component.val →
        ∀ (ch : Std.Usize) (hch : ch.val < 3),
          AspisR1PoseidonPreparedChannelUpdateInvariantV2.sumCell out c ch hc hch = AspisR1PoseidonPreparedChannelUpdateInvariantV2.sumCell initial c ch hc hch) := by
  induction fuel generalizing iter sums with
  | zero =>
      have hstop : iter.start.val ≥ iter.end.val := by omega
      have hnext := AspisR1.OccupancyRangeTraversal.next_done iter hstop
      have hstart : iter.start.val = 3 := by omega
      refine ⟨sums, ?_, ?_, ?_⟩
      · calc
          AspisR1PoseidonPreparedSum3Source.field.qm31_sum_products3_prepared_loop0_loop0_loop0
              iter left sums index right component = _ :=
            AspisR1PoseidonPreparedChannelLoopStep.generated_loop_step
              iter left sums index right component
          _ = .ok sums := by simp only [hnext, bind_tc_ok]
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
      have hcurrentBound : (AspisR1PoseidonPreparedChannelUpdateInvariantV2.sumCell sums component channel hcomponent hchannel).val ≤
          2 * (P - 1) ^ 2 := by
        rw [hcurrentRemaining]
        exact hbaseBound channel hchannel
      obtain ⟨updated, sums1, hstep, hupdatedValue, hout⟩ :=
        AspisR1PoseidonPreparedChannelRunStepLocal.runStep_success
          left sums index right component channel hindex hcomponent hchannel
          (hleft channel hchannel) (hright channel hchannel) hcurrentBound
      let product : (ch : Std.Usize) → ch.val < 3 → Nat := fun ch hch =>
        (leftCell left index component ch hindex hcomponent hch).val *
          (rightCell right component ch hcomponent hch).val
      have hupdatedValue' : updated.val =
          (AspisR1PoseidonPreparedChannelUpdateInvariantV2.sumCell sums component channel hcomponent hchannel).val + product channel hchannel := by
        simpa [AspisR1PoseidonPreparedChannelUpdateInvariantV2.sumCell, leftCell, rightCell, product,
          AspisR1PoseidonPreparedChannelRunStepLocal.at3,
          AspisR1PoseidonPreparedChannelArraySet.at3,
          AspisR1PoseidonPreparedChannelArraySet.at3] using hupdatedValue
      have hprocessedOld : ∀ (ch : Std.Usize) (hch : ch.val < 3),
          ch.val < channel.val →
          (AspisR1PoseidonPreparedChannelUpdateInvariantV2.sumCell sums component ch hcomponent hch).val =
            (AspisR1PoseidonPreparedChannelUpdateInvariantV2.sumCell initial component ch hcomponent hch).val + product ch hch := by
        intro ch hch hbefore
        exact hprocessed ch hch (by simpa [channel] using hbefore)
      have hremainingOld : ∀ (ch : Std.Usize) (hch : ch.val < 3),
          channel.val ≤ ch.val →
          AspisR1PoseidonPreparedChannelUpdateInvariantV2.sumCell sums component ch hcomponent hch = AspisR1PoseidonPreparedChannelUpdateInvariantV2.sumCell initial component ch hcomponent hch := by
        intro ch hch hafter
        exact hremaining ch hch (by simpa [channel] using hafter)
      have hinvariants :=
        AspisR1PoseidonPreparedChannelUpdateInvariantV2.update_invariants
          sums initial component channel updated hcomponent hchannel product
          hcurrentRemaining hupdatedValue' hprocessedOld hremainingOld hframe
      rcases hinvariants with ⟨hprocessedUpdate, hremainingUpdate, hframeUpdate⟩
      have hsums1 : sums1 =
          AspisR1PoseidonPreparedChannelUpdateInvariantV2.updateComponent
            sums component channel updated hcomponent := by
        change sums1 = Std.Array.set sums component
          ((AspisR1PoseidonPreparedChannelArraySet.at3 sums component hcomponent).set
            channel updated)
        simpa only [AspisR1PoseidonPreparedChannelArraySet.at3,
          AspisR1PoseidonPreparedChannelRunStepLocal.at3] using hout
      have hprocessed1 : ∀ (ch : Std.Usize) (hch : ch.val < 3), ch.val < iter1.start.val →
          (AspisR1PoseidonPreparedChannelUpdateInvariantV2.sumCell sums1 component ch hcomponent hch).val =
            (AspisR1PoseidonPreparedChannelUpdateInvariantV2.sumCell initial component ch hcomponent hch).val +
              (leftCell left index component ch hindex hcomponent hch).val *
                (rightCell right component ch hcomponent hch).val := by
        intro ch hch hj
        have hj' : ch.val < channel.val + 1 := by
          change ch.val < iter.start.val + 1
          omega
        rw [hsums1]
        simpa [product, AspisR1PoseidonPreparedChannelUpdateInvariantV2.sumCell,
          AspisR1PoseidonPreparedChannelUpdateInvariantV2.at3,
          AspisR1PoseidonPreparedChannelArraySet.at3] using hprocessedUpdate ch hch hj'
      have hremaining1 : ∀ (ch : Std.Usize) (hch : ch.val < 3), iter1.start.val ≤ ch.val →
          AspisR1PoseidonPreparedChannelUpdateInvariantV2.sumCell sums1 component ch hcomponent hch = AspisR1PoseidonPreparedChannelUpdateInvariantV2.sumCell initial component ch hcomponent hch := by
        intro ch hch hj
        have hj' : channel.val + 1 ≤ ch.val := by
          change iter.start.val + 1 ≤ ch.val
          rw [← hstart1]
          exact hj
        rw [hsums1]
        simpa [AspisR1PoseidonPreparedChannelUpdateInvariantV2.sumCell, AspisR1PoseidonPreparedChannelUpdateInvariantV2.sumCell,
          AspisR1PoseidonPreparedChannelUpdateInvariantV2.at3,
          AspisR1PoseidonPreparedChannelArraySet.at3] using hremainingUpdate ch hch hj'
      have hframe1 : ∀ (c : Std.Usize) (hc : c.val < 3), c.val ≠ component.val →
          ∀ (ch : Std.Usize) (hch : ch.val < 3),
            AspisR1PoseidonPreparedChannelUpdateInvariantV2.sumCell sums1 c ch hc hch = AspisR1PoseidonPreparedChannelUpdateInvariantV2.sumCell initial c ch hc hch := by
        intro c hc hne ch hch
        rw [hsums1]
        simpa [AspisR1PoseidonPreparedChannelUpdateInvariantV2.sumCell, AspisR1PoseidonPreparedChannelUpdateInvariantV2.sumCell,
          AspisR1PoseidonPreparedChannelUpdateInvariantV2.at3,
          AspisR1PoseidonPreparedChannelArraySet.at3] using hframeUpdate c hc hne ch hch
      obtain ⟨out, hrec, hformula, hframeOut⟩ :=
        ih sums1 iter1 hend1' hspan1 hprocessed1 hremaining1 hframe1
      refine ⟨out, ?_, hformula, hframeOut⟩
      calc
        AspisR1PoseidonPreparedSum3Source.field.qm31_sum_products3_prepared_loop0_loop0_loop0
            iter left sums index right component = _ :=
          AspisR1PoseidonPreparedChannelLoopStep.generated_loop_step
            iter left sums index right component
        _ = .ok out := by
          simp only [hnext, bind_tc_ok, channel, Loop, hstep, hrec]

#print axioms loop_success_fuel
end AspisR1PoseidonPreparedChannelLoopExact
