import NHI_SliceCells
import NHI_TensorOffsets
import NHI_ScalarStep
import NHI_CellCanon
set_option autoImplicit false
noncomputable section
namespace NHI_TensorCellTotal
open Aeneas Aeneas.Std Result ControlFlow AspisR1 LPi_FieldValues
abbrev Rev := core.iter.adapters.rev.Rev (core.ops.range.Range Usize)
abbrev next := core.iter.adapters.rev.Rev.Insts.CoreIterTraitsIteratorIterator.next
  (core.ops.range.Range.Insts.DoubleEndedIterator core.iter.range.StepUsize)

/-- Construct the actual emitted inner body from input domains. Neither its
successful return nor any output/whole-loop equality is a hypothesis. -/
theorem source (w : FIo_Native.weights.Weights) (k d n j : Usize)
    (hk : k.val<5) (hd : d.val<5) (hn : NHI_TensorDomains.Stage n.val)
    (hj : j.val<n.val) (input : Slice NQ) (len : input.val.length=64)
    (canonical : NHI_CellCanon.slice input)
    (digitCanon : NHI_CellCanon.array
      (NHI_ScalarDomain.pick (NHI_ScalarDomain.pick w.factors k.val hk) d.val hd))
    (iter cursor : Rev) (advance : next iter=ok (some j,cursor)) :
    ∃ out,FIo_Native.weights.Weights.tensor_loop0_loop0.body w k n d iter input=
      ok (cont (cursor,out)) ∧ NHI_CellCanon.slice out ∧ out.val.length=64 := by
  let row := NHI_ScalarDomain.pick w.factors k.val hk
  let digit := NHI_ScalarDomain.pick row d.val hd
  have rowRead := NHI_ScalarDomain.index w.factors k hk
  have digitRead := NHI_ScalarDomain.index row d hd
  change Array.index_usize w.factors k=ok row at rowRead
  change Array.index_usize row d=ok digit at digitRead
  let q0 := NHI_ScalarDomain.pick digit 0 (by decide)
  let q1 := NHI_ScalarDomain.pick digit 1 (by decide)
  let q2 := NHI_ScalarDomain.pick digit 2 (by decide)
  let q3 := NHI_ScalarDomain.pick digit 3 (by decide)
  have hq0 := NHI_ScalarDomain.index digit 0#usize (by decide)
  have hq1 := NHI_ScalarDomain.index digit 1#usize (by decide)
  have hq2 := NHI_ScalarDomain.index digit 2#usize (by decide)
  have hq3 := NHI_ScalarDomain.index digit 3#usize (by decide)
  change Array.index_usize digit 0#usize=ok q0 at hq0
  change Array.index_usize digit 1#usize=ok q1 at hq1
  change Array.index_usize digit 2#usize=ok q2 at hq2
  change Array.index_usize digit 3#usize=ok q3 at hq3
  have jBound : j.val < input.val.length := by
    have := NHI_TensorDomains.write_bounds n.val j.val 0 hn hj (by decide)
    omega
  let x := NHI_SliceCells.pick input j.val jBound
  have hx := NHI_SliceCells.read input j jBound
  change Slice.index_usize input j=ok x at hx
  have cx : canonQ x := NHI_CellCanon.slice_read input j x canonical hx
  have cq0 : canonQ q0 := NHI_CellCanon.array_read digit _ q0 digitCanon hq0
  have cq1 : canonQ q1 := NHI_CellCanon.array_read digit _ q1 digitCanon hq1
  have cq2 : canonQ q2 := NHI_CellCanon.array_read digit _ q2 digitCanon hq2
  have cq3 : canonQ q3 := NHI_CellCanon.array_read digit _ q3 digitCanon hq3
  obtain ⟨p0,hp0,cp0,_⟩ := LPi_TowerValues.qm_mul x q0 cx cq0
  obtain ⟨p1,hp1,cp1,_⟩ := LPi_TowerValues.qm_mul x q1 cx cq1
  obtain ⟨p2,hp2,cp2,_⟩ := LPi_TowerValues.qm_mul x q2 cx cq2
  obtain ⟨p3,hp3,cp3,_⟩ := LPi_TowerValues.qm_mul x q3 cx cq3
  let i0 := NHI_TensorOffsets.index j n 0#usize
  let i1 := NHI_TensorOffsets.index j n 1#usize
  let i2 := NHI_TensorOffsets.index j n 2#usize
  let i3 := NHI_TensorOffsets.index j n 3#usize
  have b0 : i0.val<64 := (NHI_TensorOffsets.value n j 0#usize hn hj (by decide)).2
  have b1 : i1.val<64 := (NHI_TensorOffsets.value n j 1#usize hn hj (by decide)).2
  have b2 : i2.val<64 := (NHI_TensorOffsets.value n j 2#usize hn hj (by decide)).2
  have b3 : i3.val<64 := (NHI_TensorOffsets.value n j 3#usize hn hj (by decide)).2
  let s0 := NHI_SliceCells.put input i0.val p0
  let s1 := NHI_SliceCells.put s0 i1.val p1
  let s2 := NHI_SliceCells.put s1 i2.val p2
  let out := NHI_SliceCells.put s2 i3.val p3
  have l0 : s0.val.length=64 := (NHI_SliceCells.length input i0.val p0).trans len
  have l1 : s1.val.length=64 := (NHI_SliceCells.length s0 i1.val p1).trans l0
  have l2 : s2.val.length=64 := (NHI_SliceCells.length s1 i2.val p2).trans l1
  have lo : out.val.length=64 := (NHI_SliceCells.length s2 i3.val p3).trans l2
  have hu0 := NHI_SliceCells.update input i0 (by omega) p0
  have hu1 := NHI_SliceCells.update s0 i1 (by omega) p1
  have hu2 := NHI_SliceCells.update s1 i2 (by omega) p2
  have hu3 := NHI_SliceCells.update s2 i3 (by omega) p3
  change Slice.update input i0 p0=ok s0 at hu0
  change Slice.update s0 i1 p1=ok s1 at hu1
  change Slice.update s1 i2 p2=ok s2 at hu2
  change Slice.update s2 i3 p3=ok out at hu3
  have c0 := NHI_CellCanon.put input i0.val p0 canonical cp0
  have c1 := NHI_CellCanon.put s0 i1.val p1 c0 cp1
  have c2 := NHI_CellCanon.put s1 i2.val p2 c1 cp2
  have co := NHI_CellCanon.put s2 i3.val p3 c2 cp3
  refine ⟨out,?_,co,lo⟩
  simp only [next] at advance
  simp only [i0,i1,i2,i3,NHI_TensorOffsets.index] at hu0 hu1 hu2 hu3
  unfold FIo_Native.weights.Weights.tensor_loop0_loop0.body
  rw [advance]
  simp only [bind_tc_ok]
  dsimp! only
  simp only [hx,rowRead,digitRead,hq0,hq1,hq2,hq3,hp0,hp1,hp2,hp3,lift,bind_tc_ok,hu0,hu1,hu2,hu3]

#print axioms source
end NHI_TensorCellTotal
