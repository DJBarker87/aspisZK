import AspisR1PoseidonPreparedChannelLoopExact
import OccupancyRangeTraversal

set_option autoImplicit false
namespace AspisR1PoseidonPreparedComponentLoopExact
open Aeneas Aeneas.Std Result
open AspisR1SelectedMaskProbe

abbrev U64 := UScalar UScalarTy.U64
abbrev P : Nat := 2147483647
abbrev Sums := Array (Array U64 3#usize) 3#usize
abbrev PreparedArray := Array field.PreparedQm31Multiplier 3#usize
abbrev ComponentArray := Array (Array field.M31 3#usize) 3#usize
abbrev Range := core.ops.range.Range Std.Usize
abbrev Loop := AspisR1PoseidonPreparedSum3Source.field.qm31_sum_products3_prepared_loop0_loop0
abbrev InnerLoop := AspisR1PoseidonPreparedSum3Source.field.qm31_sum_products3_prepared_loop0_loop0_loop0
abbrev sumCell := AspisR1PoseidonPreparedChannelUpdateInvariantV2.sumCell

private def leftCell (left : PreparedArray) (index component channel : Std.Usize)
    (hi : index.val < 3) (hc : component.val < 3) (hch : channel.val < 3) : field.M31 :=
  AspisR1PoseidonPreparedChannelRunStepLocal.at3
    (AspisR1PoseidonPreparedChannelRunStepLocal.at3
      (AspisR1PoseidonPreparedChannelRunStepLocal.at3 left index hi).components component hc)
    channel hch

private def rightCell (right : ComponentArray) (component channel : Std.Usize)
    (hc : component.val < 3) (hch : channel.val < 3) : field.M31 :=
  AspisR1PoseidonPreparedChannelRunStepLocal.at3
    (AspisR1PoseidonPreparedChannelRunStepLocal.at3 right component hc) channel hch

private def product (left : PreparedArray) (right : ComponentArray)
    (index component channel : Std.Usize) (hi : index.val < 3)
    (hc : component.val < 3) (hch : channel.val < 3) : Nat :=
  (leftCell left index component channel hi hc hch).val *
    (rightCell right component channel hc hch).val

private theorem generated_loop_step
    (iter : Range) (left : PreparedArray) (sums : Sums) (index : Std.Usize)
    (right : ComponentArray) :
    AspisR1PoseidonPreparedSum3Source.field.qm31_sum_products3_prepared_loop0_loop0
      iter left sums index right = (do
      let (o, iter1) ← core.iter.range.IteratorRange.next core.iter.range.StepUsize iter
      match o with
      | none => .ok sums
      | some component => do
          let sums1 ← InnerLoop { start := 0#usize, «end» := 3#usize }
            left sums index right component
          Loop iter1 left sums1 index right) := by
  rw [AspisR1PoseidonPreparedSum3Source.field.qm31_sum_products3_prepared_loop0_loop0.eq_def]
  rfl

/-- Exact execution of the actual outer component loop. Each processed
component receives the corresponding prepared product in all three channels. -/
theorem loop_success_fuel
    (left : PreparedArray) (initial sums : Sums) (index : Std.Usize)
    (right : ComponentArray) (iter : Range) (fuel : Nat)
    (hindex : index.val < 3)
    (hend : iter.end.val = 3) (hspan : iter.start.val + fuel = 3)
    (hleft : ∀ (c ch : Std.Usize) (hc : c.val < 3) (hch : ch.val < 3),
      (leftCell left index c ch hindex hc hch).val < P)
    (hright : ∀ (c ch : Std.Usize) (hc : c.val < 3) (hch : ch.val < 3),
      (rightCell right c ch hc hch).val < P)
    (hbaseBound : ∀ (c ch : Std.Usize) (hc : c.val < 3) (hch : ch.val < 3),
      (sumCell initial c ch hc hch).val ≤ 2 * (P - 1) ^ 2)
    (hprocessed : ∀ (c ch : Std.Usize) (hc : c.val < 3) (hch : ch.val < 3),
      c.val < iter.start.val →
      (sumCell sums c ch hc hch).val =
        (sumCell initial c ch hc hch).val + product left right index c ch hindex hc hch)
    (hremaining : ∀ (c ch : Std.Usize) (hc : c.val < 3) (hch : ch.val < 3),
      iter.start.val ≤ c.val → sumCell sums c ch hc hch = sumCell initial c ch hc hch) :
    ∃ out : Sums,
      Loop iter left sums index right = .ok out ∧
      (∀ (c ch : Std.Usize) (hc : c.val < 3) (hch : ch.val < 3),
        (sumCell out c ch hc hch).val =
          (sumCell initial c ch hc hch).val + product left right index c ch hindex hc hch) := by
  induction fuel generalizing initial sums iter with
  | zero =>
      have hstop : iter.start.val ≥ iter.end.val := by omega
      have hnext := AspisR1.OccupancyRangeTraversal.next_done iter hstop
      have hstart : iter.start.val = 3 := by omega
      refine ⟨sums, ?_, ?_⟩
      · calc
          Loop iter left sums index right = _ := generated_loop_step iter left sums index right
          _ = .ok sums := by simp only [hnext, bind_tc_ok]
      · intro c ch hc hch
        exact hprocessed c ch hc hch (by omega)
  | succ fuel ih =>
      have hlt : iter.start.val < iter.end.val := by omega
      have hcomponentBound : iter.start.val < 3 := by omega
      obtain ⟨iter1, hnext, hstart1, hend1, _⟩ :=
        AspisR1.OccupancyRangeTraversal.next_step iter hlt
      have hend1' : iter1.end.val = 3 := by rw [hend1, hend]
      have hspan1 : iter1.start.val + fuel = 3 := by omega
      let component := iter.start
      have hcomponent : component.val < 3 := by simpa [component] using hcomponentBound
      have hcomponentStart : component.val = iter.start.val := rfl
      have hrowUnchanged : ∀ (ch : Std.Usize) (hch : ch.val < 3),
          sumCell sums component ch hcomponent hch = sumCell initial component ch hcomponent hch := by
        intro ch hch
        exact hremaining component ch hcomponent hch (by simp [component])
      have hinnerBound : ∀ (ch : Std.Usize) (hch : ch.val < 3),
          (sumCell sums component ch hcomponent hch).val ≤ 2 * (P - 1) ^ 2 := by
        intro ch hch
        rw [hrowUnchanged]
        exact hbaseBound component ch hcomponent hch
      obtain ⟨sums1, hinner, hinnerValue, hinnerFrame⟩ :=
        AspisR1PoseidonPreparedChannelLoopExact.loop_success_fuel
          left right index component sums sums { start := 0#usize, «end» := 3#usize } 3
          hindex hcomponent (by scalar_tac) (by scalar_tac)
          (by intro ch hch; exact hleft component ch hcomponent hch)
          (by intro ch hch; exact hright component ch hcomponent hch)
          hinnerBound
          (by
            intro ch hch hbefore
            have hzero : (0#usize).val = 0 := by scalar_tac
            change ch.val < 0 at hbefore
            omega)
          (by intro ch hch hafter; rfl)
          (by intro c hc hne ch hch; rfl)
      have hprocessed1 : ∀ (c ch : Std.Usize) (hc : c.val < 3) (hch : ch.val < 3),
          c.val < iter1.start.val →
          (sumCell sums1 c ch hc hch).val =
            (sumCell initial c ch hc hch).val + product left right index c ch hindex hc hch := by
        intro c ch hc hch hj
        by_cases hbefore : c.val < component.val
        · have hne : c.val ≠ component.val := by omega
          have hframe := hinnerFrame c hc hne ch hch
          change (AspisR1PoseidonPreparedChannelUpdateInvariantV2.sumCell sums1 c ch hc hch).val = _
          rw [hframe]
          exact hprocessed c ch hc hch (by simpa [component] using hbefore)
        · have heq : c.val = component.val := by omega
          have hcEq : c = component := UScalar.eq_of_val_eq heq
          subst c
          have hformula := hinnerValue ch hch
          change (AspisR1PoseidonPreparedChannelUpdateInvariantV2.sumCell sums1 component ch hcomponent hch).val =
            (AspisR1PoseidonPreparedChannelUpdateInvariantV2.sumCell sums component ch hcomponent hch).val +
              (leftCell left index component ch hindex hcomponent hch).val *
                (rightCell right component ch hcomponent hch).val at hformula
          have hrowUnchanged' :
              AspisR1PoseidonPreparedChannelUpdateInvariantV2.sumCell sums component ch hcomponent hch =
                AspisR1PoseidonPreparedChannelUpdateInvariantV2.sumCell initial component ch hcomponent hch := by
            simpa only [sumCell] using hrowUnchanged ch hch
          rw [hrowUnchanged'] at hformula
          have hproof : hc = hcomponent := Subsingleton.elim _ _
          subst hc
          simpa only [product] using hformula
      have hremaining1 : ∀ (c ch : Std.Usize) (hc : c.val < 3) (hch : ch.val < 3),
          iter1.start.val ≤ c.val → sumCell sums1 c ch hc hch = sumCell initial c ch hc hch := by
        intro c ch hc hch hj
        have hcomponentNext : component.val + 1 = iter1.start.val := by
          simpa only [component] using hstart1.symm
        have hafter : component.val ≤ c.val := by omega
        have hne : c.val ≠ component.val := by omega
        change AspisR1PoseidonPreparedChannelUpdateInvariantV2.sumCell sums1 c ch hc hch =
          AspisR1PoseidonPreparedChannelUpdateInvariantV2.sumCell initial c ch hc hch
        exact (hinnerFrame c hc hne ch hch).trans
          (hremaining c ch hc hch (by simpa [component] using hafter))
      obtain ⟨out, hrec, hformula⟩ :=
        ih initial sums1 iter1 hend1' hspan1 hbaseBound hprocessed1 hremaining1
      have hinner' :
          AspisR1PoseidonPreparedSum3Source.field.qm31_sum_products3_prepared_loop0_loop0_loop0
            { start := 0#usize, «end» := 3#usize } left sums index right iter.start = .ok sums1 := by
        simpa only [component, InnerLoop, AspisR1PoseidonPreparedChannelLoopExact.Loop] using hinner
      have hrec' :
          AspisR1PoseidonPreparedSum3Source.field.qm31_sum_products3_prepared_loop0_loop0
            iter1 left sums1 index right = .ok out := by
        simpa only [Loop] using hrec
      refine ⟨out, ?_, hformula⟩
      calc
        Loop iter left sums index right = _ := generated_loop_step iter left sums index right
        _ = .ok out := by simp only [hnext, bind_tc_ok, hinner', hrec']

#print axioms loop_success_fuel
end AspisR1PoseidonPreparedComponentLoopExact
