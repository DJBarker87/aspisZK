import RPu_AspisR1_PoseidonPreparedIndexComponentsCanonical
import RPu_AspisR1_PoseidonPreparedIndexProductBounds
import OccupancyRangeTraversal

set_option autoImplicit false
namespace AspisR1PoseidonPreparedIndexLoopExactV2
open Aeneas Aeneas.Std Result
open AspisR1SelectedMaskProbe
open AspisR1.ExtractedMaskTowerAdd

abbrev P : Nat := 2147483647
abbrev Q : Nat := AspisR1PoseidonPreparedIndexProductBounds.Q
abbrev PreparedArray := Array field.PreparedQm31Multiplier 3#usize
abbrev RightArray := Array field.QM31 3#usize
abbrev Sums := Array (Array (UScalar UScalarTy.U64) 3#usize) 3#usize
abbrev Components := Array (Array field.M31 3#usize) 3#usize
abbrev Range := core.ops.range.Range Std.Usize
abbrev Loop := AspisR1PoseidonPreparedSum3Source.field.qm31_sum_products3_prepared_loop0
abbrev ComponentLoop := AspisR1PoseidonPreparedSum3Source.field.qm31_sum_products3_prepared_loop0_loop0


def uFin (i : Fin 3) : Std.Usize := AspisR1PoseidonPreparedIndexProductBounds.uFin i

private def tableCell (table : Components) (component channel : Std.Usize)
    (hc : component.val < 3) (hch : channel.val < 3) : field.M31 :=
  AspisR1PoseidonPreparedChannelRunStepLocal.at3
    (AspisR1PoseidonPreparedChannelRunStepLocal.at3 table component hc) channel hch

private def leftCell (left : PreparedArray) (index component channel : Std.Usize)
    (hi : index.val < 3) (hc : component.val < 3) (hch : channel.val < 3) : field.M31 :=
  AspisR1PoseidonPreparedChannelRunStepLocal.at3
    (AspisR1PoseidonPreparedChannelRunStepLocal.at3
      (AspisR1PoseidonPreparedChannelRunStepLocal.at3 left index hi).components component hc)
    channel hch

private def sumCell (sums : Sums) (component channel : Std.Usize)
    (hc : component.val < 3) (hch : channel.val < 3) : UScalar UScalarTy.U64 :=
  AspisR1PoseidonPreparedChannelUpdateInvariantV2.sumCell sums component channel hc hch

private theorem generated_index_loop_step
    (iter : Range) (left : PreparedArray) (right : RightArray) (sums : Sums) :
    Loop iter left right sums = (do
      let (o, iter1) ← core.iter.range.IteratorRange.next core.iter.range.StepUsize iter
      match o with
      | none => .ok sums
      | some index => do
          let q ← Array.index_usize right index
          let rightSum ← field.CM31.add q.c0 q.c1
          let m ← field.M31.add q.c0.a q.c0.b
          let m1 ← field.M31.add q.c1.a q.c1.b
          let m2 ← field.M31.add rightSum.a rightSum.b
          let components : Components := Array.make 3#usize [
            Array.make 3#usize [q.c0.a, q.c0.b, m],
            Array.make 3#usize [q.c1.a, q.c1.b, m1],
            Array.make 3#usize [rightSum.a, rightSum.b, m2]]
          let sums1 ← ComponentLoop { start := 0#usize, «end» := 3#usize }
            left sums index components
          Loop iter1 left right sums1) := by
  exact AspisR1PoseidonPreparedIndexLoopStep.generated_index_loop_step iter left right sums

theorem loop_success_fuel
    (left : PreparedArray) (right : RightArray) (sums : Sums)
    (tables : Fin 3 → Components) (rightValues : Fin 3 → field.QM31)
    (iter : Range) (fuel : Nat)
    (hend : iter.end.val = 3) (hspan : iter.start.val + fuel = 3)
    (hleft : ∀ (i : Fin 3) (c ch : Std.Usize) (hc : c.val < 3) (hch : ch.val < 3),
      (leftCell left (AspisR1PoseidonPreparedIndexProductBounds.uFin i) c ch
        (by rw [AspisR1PoseidonPreparedIndexProductBounds.uFin_val]; exact i.isLt) hc hch).val < P)
    (hrightValue : ∀ i : Fin 3,
      Array.index_usize right (AspisR1PoseidonPreparedIndexProductBounds.uFin i) = .ok (rightValues i))
    (hbuild : ∀ i : Fin 3,
      (do
        let rightSum ← field.CM31.add (rightValues i).c0 (rightValues i).c1
        let m ← field.M31.add (rightValues i).c0.a (rightValues i).c0.b
        let m1 ← field.M31.add (rightValues i).c1.a (rightValues i).c1.b
        let m2 ← field.M31.add rightSum.a rightSum.b
        ok (Array.make 3#usize [
          (Array.make 3#usize [(rightValues i).c0.a, (rightValues i).c0.b, m] : Array field.M31 3#usize),
          (Array.make 3#usize [(rightValues i).c1.a, (rightValues i).c1.b, m1] : Array field.M31 3#usize),
          (Array.make 3#usize [rightSum.a, rightSum.b, m2] : Array field.M31 3#usize)] : Components)) = .ok (tables i))
    (htable : ∀ (i : Fin 3) (c ch : Std.Usize) (hc : c.val < 3) (hch : ch.val < 3),
      (tableCell (tables i) c ch hc hch).val < P)
    (hmodel : ∀ (c ch : Std.Usize) (hc : c.val < 3) (hch : ch.val < 3),
      (sumCell sums c ch hc hch).val =
        AspisR1PoseidonPreparedIndexProductBounds.prefixProduct left tables iter.start.val c ch hc hch) :
    ∃ out : Sums,
      Loop iter left right sums = .ok out ∧
      (∀ (c ch : Std.Usize) (hc : c.val < 3) (hch : ch.val < 3),
        (sumCell out c ch hc hch).val =
          AspisR1PoseidonPreparedIndexProductBounds.prefixProduct left tables 3 c ch hc hch) := by
  induction fuel generalizing sums iter with
  | zero =>
      have hstop : iter.start.val ≥ iter.end.val := by omega
      have hnext := AspisR1.OccupancyRangeTraversal.next_done iter hstop
      have hstart : iter.start.val = 3 := by omega
      refine ⟨sums, ?_, ?_⟩
      · calc
          Loop iter left right sums = _ := generated_index_loop_step iter left right sums
          _ = .ok sums := by simp only [hnext, bind_tc_ok]
      · intro c ch hc hch
        rw [hmodel c ch hc hch, hstart]
  | succ fuel ih =>
      have hlt : iter.start.val < iter.end.val := by omega
      have hidx : iter.start.val < 3 := by omega
      obtain ⟨iter1, hnext, hstart1, hend1, _⟩ := AspisR1.OccupancyRangeTraversal.next_step iter hlt
      have hend1' : iter1.end.val = 3 := by rw [hend1, hend]
      have hspan1 : iter1.start.val + fuel = 3 := by omega
      let index : Fin 3 := ⟨iter.start.val, hidx⟩
      have hindexValue : index.val = iter.start.val := rfl
      have hu : AspisR1PoseidonPreparedIndexProductBounds.uFin index = iter.start := by
        apply UScalar.eq_of_val_eq
        rw [AspisR1PoseidonPreparedIndexProductBounds.uFin_val]
      have hleftBound : ∀ (c ch : Std.Usize) (hc : c.val < 3) (hch : ch.val < 3),
          (leftCell left iter.start c ch hidx hc hch).val < P := by
        intro c ch hc hch
        simpa [hu] using hleft index c ch hc hch
      have hrightBound : ∀ (c ch : Std.Usize) (hc : c.val < 3) (hch : ch.val < 3),
          (tableCell (tables index) c ch hc hch).val < P :=
        htable index
      have haccBound : ∀ (c ch : Std.Usize) (hc : c.val < 3) (hch : ch.val < 3),
          (sumCell sums c ch hc hch).val ≤ 2 * Q := by
        intro c ch hc hch
        have hp := AspisR1PoseidonPreparedIndexProductBounds.prefixProduct_le
          left tables hleft htable iter.start.val c ch hc hch
        have hm := hmodel c ch hc hch
        have hsmall : iter.start.val ≤ 2 := by omega
        have hQ : 0 ≤ Q := by dsimp [Q, AspisR1PoseidonPreparedIndexProductBounds.Q, AspisR1PoseidonPreparedIndexProductBounds.P, P]; omega
        nlinarith
      obtain ⟨sums1, hinner, hinnerValue⟩ :=
        AspisR1PoseidonPreparedComponentLoopExact.loop_success_fuel
          left sums sums iter.start (tables index) { start := 0#usize, «end» := 3#usize } 3
          hidx (by scalar_tac) (by scalar_tac)
          (by exact hleftBound)
          (by exact hrightBound)
          haccBound
          (by intro c ch hc hch hbefore; change c.val < 0 at hbefore; omega)
          (by intro c ch hc hch hafter; rfl)
      have hmodel1 : ∀ (c ch : Std.Usize) (hc : c.val < 3) (hch : ch.val < 3),
          (sumCell sums1 c ch hc hch).val =
            AspisR1PoseidonPreparedIndexProductBounds.prefixProduct left tables iter1.start.val c ch hc hch := by
        intro c ch hc hch
        have hv := hinnerValue c ch hc hch
        change (sumCell sums1 c ch hc hch).val = (sumCell sums c ch hc hch).val +
          (leftCell left iter.start c ch hidx hc hch).val *
            (tableCell (tables index) c ch hc hch).val at hv
        have hcur := hmodel c ch hc hch
        have hfin : (⟨iter.start.val % 3, Nat.mod_lt _ (by omega)⟩ : Fin 3) = index := by
          apply Fin.ext
          simp [index]
          omega
        have hprefix := AspisR1PoseidonPreparedIndexProductBounds.prefixProduct_succ
          left tables iter.start.val c ch hc hch
        rw [← hstart1] at hprefix
        rw [hfin] at hprefix
        rw [hv, hcur]
        exact hprefix.symm
      obtain ⟨out, hrec, hformula⟩ := ih sums1 iter1 hend1' hspan1 hmodel1
      have hread : Array.index_usize right iter.start = .ok (rightValues index) := by
        simpa [hu] using hrightValue index
      have hinner' : ComponentLoop { start := 0#usize, «end» := 3#usize }
          left sums iter.start (tables index) = .ok sums1 := by
        simpa only [AspisR1PoseidonPreparedComponentLoopExact.Loop] using hinner
      have hrec' : Loop iter1 left right sums1 = .ok out := hrec
      refine ⟨out, ?_, hformula⟩
      have hbuildContinue :
          (do
            let components ← (do
              let rightSum ← field.CM31.add (rightValues index).c0 (rightValues index).c1
              let m ← field.M31.add (rightValues index).c0.a (rightValues index).c0.b
              let m1 ← field.M31.add (rightValues index).c1.a (rightValues index).c1.b
              let m2 ← field.M31.add rightSum.a rightSum.b
              ok (Array.make 3#usize [
                (Array.make 3#usize [(rightValues index).c0.a, (rightValues index).c0.b, m] : Array field.M31 3#usize),
                (Array.make 3#usize [(rightValues index).c1.a, (rightValues index).c1.b, m1] : Array field.M31 3#usize),
                (Array.make 3#usize [rightSum.a, rightSum.b, m2] : Array field.M31 3#usize)] : Components))
            let sums1 ← ComponentLoop { start := 0#usize, «end» := 3#usize }
              left sums iter.start components
            Loop iter1 left right sums1) =
          (do
            let components ← .ok (tables index)
            let sums1 ← ComponentLoop { start := 0#usize, «end» := 3#usize }
              left sums iter.start components
            Loop iter1 left right sums1) := by
        have h := congrArg (fun built : Result Components => do
          let components ← built
          let sums1 ← ComponentLoop { start := 0#usize, «end» := 3#usize }
            left sums iter.start components
          Loop iter1 left right sums1) (hbuild index)
        simpa only [bind_assoc_eq] using h
      calc
        Loop iter left right sums = _ := generated_index_loop_step iter left right sums
        _ = (do
          let components ← (do
            let rightSum ← field.CM31.add (rightValues index).c0 (rightValues index).c1
            let m ← field.M31.add (rightValues index).c0.a (rightValues index).c0.b
            let m1 ← field.M31.add (rightValues index).c1.a (rightValues index).c1.b
            let m2 ← field.M31.add rightSum.a rightSum.b
            ok (Array.make 3#usize [
              (Array.make 3#usize [(rightValues index).c0.a, (rightValues index).c0.b, m] : Array field.M31 3#usize),
              (Array.make 3#usize [(rightValues index).c1.a, (rightValues index).c1.b, m1] : Array field.M31 3#usize),
              (Array.make 3#usize [rightSum.a, rightSum.b, m2] : Array field.M31 3#usize)] : Components))
          let sums1 ← ComponentLoop { start := 0#usize, «end» := 3#usize }
            left sums iter.start components
          Loop iter1 left right sums1) := by
            simp only [hnext, bind_tc_ok, hread, bind_assoc_eq]
        _ = (do
          let components ← .ok (tables index)
          let sums1 ← ComponentLoop { start := 0#usize, «end» := 3#usize }
            left sums iter.start components
          Loop iter1 left right sums1) := hbuildContinue
        _ = .ok out := by simp only [bind_tc_ok, hinner', hrec']
end AspisR1PoseidonPreparedIndexLoopExactV2
