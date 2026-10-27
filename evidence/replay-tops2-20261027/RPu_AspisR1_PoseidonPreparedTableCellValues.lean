import RPu_AspisR1_PoseidonPreparedTableValues
import RPu_AspisR1PoseidonPreparedChannelRunStepLocal

set_option autoImplicit false
namespace AspisR1.PoseidonPreparedTableCellValues
open Aeneas.Std Result AspisR1SelectedMaskProbe

abbrev QM := field.QM31
abbrev M31 := field.M31
abbrev Components := Array (Array M31 3#usize) 3#usize

private def at3 {α : Type} (a : Array α 3#usize) (i : Usize) (hi : i.val < 3) : α :=
  AspisR1PoseidonPreparedChannelRunStepLocal.at3 a i hi

private def cell (table : Components) (c ch : Usize)
    (hc : c.val < 3) (hch : ch.val < 3) : M31 :=
  at3 (at3 table c hc) ch hch

theorem table_cells (q : QM) (hq : AspisR1.PoseidonPreparedTableValues.CanonicalQM q)
    (table : Components)
    (hbuild : (do
      let rightSum ← field.CM31.add q.c0 q.c1
      let m0 ← field.M31.add q.c0.a q.c0.b
      let m1 ← field.M31.add q.c1.a q.c1.b
      let m2 ← field.M31.add rightSum.a rightSum.b
      ok (Array.make 3#usize [
        (Array.make 3#usize [q.c0.a,q.c0.b,m0] : Array M31 3#usize),
        (Array.make 3#usize [q.c1.a,q.c1.b,m1] : Array M31 3#usize),
        (Array.make 3#usize [rightSum.a,rightSum.b,m2] : Array M31 3#usize)] : Components)) = .ok table) :
    ∃ rightSum m0 m1 m2,
      field.CM31.add q.c0 q.c1 = .ok rightSum ∧
      field.M31.add q.c0.a q.c0.b = .ok m0 ∧
      field.M31.add q.c1.a q.c1.b = .ok m1 ∧
      field.M31.add rightSum.a rightSum.b = .ok m2 ∧
      cell table 0#usize 0#usize (by scalar_tac) (by scalar_tac) = q.c0.a ∧
      cell table 0#usize 1#usize (by scalar_tac) (by scalar_tac) = q.c0.b ∧
      cell table 0#usize 2#usize (by scalar_tac) (by scalar_tac) = m0 ∧
      cell table 1#usize 0#usize (by scalar_tac) (by scalar_tac) = q.c1.a ∧
      cell table 1#usize 1#usize (by scalar_tac) (by scalar_tac) = q.c1.b ∧
      cell table 1#usize 2#usize (by scalar_tac) (by scalar_tac) = m1 ∧
      cell table 2#usize 0#usize (by scalar_tac) (by scalar_tac) = rightSum.a ∧
      cell table 2#usize 1#usize (by scalar_tac) (by scalar_tac) = rightSum.b ∧
      cell table 2#usize 2#usize (by scalar_tac) (by scalar_tac) = m2 := by
  obtain ⟨rightSum,m0,m1,m2,components,hsum,hm0,hm1,hm2,_,_,_,hsource,hcomponents⟩ :=
    AspisR1.PoseidonPreparedTableValues.actual_components_values q hq
  have htable : table = Array.make 3#usize [
      (Array.make 3#usize [q.c0.a,q.c0.b,m0] : Array M31 3#usize),
      (Array.make 3#usize [q.c1.a,q.c1.b,m1] : Array M31 3#usize),
      (Array.make 3#usize [rightSum.a,rightSum.b,m2] : Array M31 3#usize)] := by
    have hct : components = table := Result.ok.inj (hsource.symm.trans hbuild)
    exact hct.symm.trans hcomponents
  refine ⟨rightSum,m0,m1,m2,hsum,hm0,hm1,hm2,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩ <;>
    simp [cell, at3, AspisR1PoseidonPreparedChannelRunStepLocal.at3,
      htable, Array.make]

#print axioms table_cells
end AspisR1.PoseidonPreparedTableCellValues
