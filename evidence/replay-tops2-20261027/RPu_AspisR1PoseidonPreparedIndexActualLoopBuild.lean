import RPu_AspisR1.PoseidonPreparedIndexLoopExactV2Fix4
import RPu_AspisR1.PoseidonPreparedIndexComponentsCanonical
import RPu_AspisR1PoseidonPreparedChannelArraySpecs

set_option autoImplicit false
namespace AspisR1PoseidonPreparedIndexActualLoopBuild
open Aeneas Aeneas.Std Result
open AspisR1SelectedMaskProbe

abbrev P : Nat := 2147483647
abbrev CanonicalQM := AspisR1.ExtractedMaskQM31Exact.CurrentCanonicalQM
abbrev PreparedArray := Array field.PreparedQm31Multiplier 3#usize
abbrev RightArray := Array field.QM31 3#usize
abbrev Sums := Array (Array (UScalar UScalarTy.U64) 3#usize) 3#usize
abbrev Components := Array (Array field.M31 3#usize) 3#usize
abbrev Range := core.ops.range.Range Std.Usize
abbrev Loop := AspisR1PoseidonPreparedSum3Source.field.qm31_sum_products3_prepared_loop0
abbrev uFin := AspisR1PoseidonPreparedIndexProductBounds.uFin
private def leftCell (left : PreparedArray) (index component channel : Std.Usize)
    (hi : index.val < 3) (hc : component.val < 3) (hch : channel.val < 3) : field.M31 :=
  AspisR1PoseidonPreparedChannelRunStepLocal.at3
    (AspisR1PoseidonPreparedChannelRunStepLocal.at3
      (AspisR1PoseidonPreparedChannelRunStepLocal.at3 left index hi).components component hc)
    channel hch
abbrev sumCell := AspisR1PoseidonPreparedChannelUpdateInvariantV2.sumCell
private def tableCell (table : Components) (component channel : Std.Usize)
    (hc : component.val < 3) (hch : channel.val < 3) : field.M31 :=
  AspisR1PoseidonPreparedChannelRunStepLocal.at3
    (AspisR1PoseidonPreparedChannelRunStepLocal.at3 table component hc) channel hch

private def rightAt (right : RightArray) (i : Fin 3) : field.QM31 :=
  right.val[(uFin i).val]'(by
    have hu := AspisR1PoseidonPreparedIndexProductBounds.uFin_val i
    simpa [right.property, hu] using i.isLt)

theorem actual_loop_success
    (left : PreparedArray) (right : RightArray) (initial : Sums)
    (hleft : ∀ (i : Fin 3) (c ch : Std.Usize) (hc : c.val < 3) (hch : ch.val < 3),
      (leftCell left (uFin i) c ch
        (by rw [AspisR1PoseidonPreparedIndexProductBounds.uFin_val]; exact i.isLt) hc hch).val < P)
    (hrightCanonical : ∀ i : Fin 3, CanonicalQM (rightAt right i))
    (hinitial : ∀ (c ch : Std.Usize) (hc : c.val < 3) (hch : ch.val < 3),
      (sumCell initial c ch hc hch).val = 0) :
    ∃ tables : Fin 3 → Components, ∃ out : Sums,
      Loop { start := 0#usize, «end» := 3#usize } left right initial = .ok out ∧
      (∀ (c ch : Std.Usize) (hc : c.val < 3) (hch : ch.val < 3),
        (sumCell out c ch hc hch).val =
          AspisR1PoseidonPreparedIndexProductBounds.prefixProduct left tables 3 c ch hc hch) ∧
      (∀ i : Fin 3,
        (do
          let rightSum ← field.CM31.add (rightAt right i).c0 (rightAt right i).c1
          let m ← field.M31.add (rightAt right i).c0.a (rightAt right i).c0.b
          let m1 ← field.M31.add (rightAt right i).c1.a (rightAt right i).c1.b
          let m2 ← field.M31.add rightSum.a rightSum.b
          ok (Array.make 3#usize [
            (Array.make 3#usize [(rightAt right i).c0.a, (rightAt right i).c0.b, m] : Array field.M31 3#usize),
            (Array.make 3#usize [(rightAt right i).c1.a, (rightAt right i).c1.b, m1] : Array field.M31 3#usize),
            (Array.make 3#usize [rightSum.a, rightSum.b, m2] : Array field.M31 3#usize)] : Components)) = .ok (tables i)) := by
  classical
  let tables : Fin 3 → Components := fun i =>
    Classical.choose (AspisR1PoseidonPreparedIndexComponentsCanonical.actual_components_canonical
      (rightAt right i) (hrightCanonical i))
  have htable : ∀ (i : Fin 3) (c ch : Std.Usize) (hc : c.val < 3) (hch : ch.val < 3),
      (tableCell (tables i) c ch hc hch).val < P := by
    intro i c ch hc hch
    exact (Classical.choose_spec
      (AspisR1PoseidonPreparedIndexComponentsCanonical.actual_components_canonical
        (rightAt right i) (hrightCanonical i))).2 c ch hc hch
  have hbuild : ∀ i : Fin 3,
      (do
        let rightSum ← field.CM31.add (rightAt right i).c0 (rightAt right i).c1
        let m ← field.M31.add (rightAt right i).c0.a (rightAt right i).c0.b
        let m1 ← field.M31.add (rightAt right i).c1.a (rightAt right i).c1.b
        let m2 ← field.M31.add rightSum.a rightSum.b
        ok (Array.make 3#usize [
          (Array.make 3#usize [(rightAt right i).c0.a, (rightAt right i).c0.b, m] : Array field.M31 3#usize),
          (Array.make 3#usize [(rightAt right i).c1.a, (rightAt right i).c1.b, m1] : Array field.M31 3#usize),
          (Array.make 3#usize [rightSum.a, rightSum.b, m2] : Array field.M31 3#usize)] : Components)) = .ok (tables i) := by
    intro i
    exact (Classical.choose_spec
      (AspisR1PoseidonPreparedIndexComponentsCanonical.actual_components_canonical
        (rightAt right i) (hrightCanonical i))).1
  have hrightValue : ∀ i : Fin 3,
      Array.index_usize right (uFin i) = .ok (rightAt right i) := by
    intro i
    obtain ⟨q, hread, hq⟩ := AspisR1PoseidonPreparedChannelArraySpecs.index_ok right (uFin i)
      (by rw [AspisR1PoseidonPreparedIndexProductBounds.uFin_val]; exact i.isLt)
    calc
      Array.index_usize right (uFin i) = .ok q := hread
      _ = .ok (rightAt right i) := by
        have hq' : q = rightAt right i := by simpa [rightAt] using hq
        rw [hq']
  have hmodel : ∀ (c ch : Std.Usize) (hc : c.val < 3) (hch : ch.val < 3),
      (sumCell initial c ch hc hch).val =
        AspisR1PoseidonPreparedIndexProductBounds.prefixProduct left tables 0 c ch hc hch := by
    intro c ch hc hch
    rw [hinitial]
    rfl
  obtain ⟨out, hrun, hout⟩ :=
    AspisR1PoseidonPreparedIndexLoopExactV2.loop_success_fuel
      left right initial tables (fun i => rightAt right i)
      { start := 0#usize, «end» := 3#usize } 3
      (by scalar_tac) (by scalar_tac)
      hleft hrightValue hbuild htable hmodel
  exact ⟨tables, out, hrun, hout, hbuild⟩

#print axioms actual_loop_success
end AspisR1PoseidonPreparedIndexActualLoopBuild
