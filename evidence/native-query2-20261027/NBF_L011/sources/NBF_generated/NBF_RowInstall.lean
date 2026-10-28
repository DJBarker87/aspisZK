import NBF_LoopFrame
open Aeneas Aeneas.Std Result ControlFlow
set_option autoImplicit false
namespace NBF_RowInstall
open AspisR1 AspisR1Stage2 Port3_NativeQueryBody
abbrev Q := aspis_core.field.QM31
abbrev E := Stage2E
def zeroQ : Q := ⟨⟨0#u32,0#u32⟩,⟨0#u32,0#u32⟩⟩
def embedQ (q : Q) : E := ⟨q,zeroQ⟩
def embedM (m : U32) : E := ⟨⟨⟨m,0#u32⟩,⟨0#u32,0#u32⟩⟩,zeroQ⟩
/-- Explicit direct cohort row callbacks. Native embedding correspondence is
checked separately on canonical inputs; no arbitrary callback is hidden. -/
def install (ops : Ops) : Ops :=
 {ops with
  op1:=fun q=>ok (embedQ q)
  op10:=fun m=>ok (embedM m)
  op12:=fun s j=>core.slice.index.Slice.index
    (core.slice.index.SliceIndexUsizeSlice Q) s j
  op13:=fun basis j=>Array.index_usize basis j
  op14:=Port3_NativeRowFrame.push
  op15:=fun _ _ _=>ok ()}

theorem body (ops : Ops) (v : alloc.vec.Vec Q) (q : Q) (next : Usize)
 (basis : Array U32 256#usize) (iter : core.ops.range.Range Usize)
 (b : verifier.BatchedWeights) (x : Fin 4 → U64)
 (width : iter.end.val=64) (active : iter.start.val<64)
 (v64 : v.val.length=64)
 (inv : NBB_Sweep.Inv b.terms.val iter.start.val b.raw)
 (read : b.raw.val[iter.start.val]?=some (S7Kani2OwnedRowRefinement.makeRow x))
 (hq : ∀ k, (S7Kani2OwnedRowRefinement.powerLimb (Port3_RowsInstall.toK q) k).val<2^31-1)
 (hb : ∀ j, j<64 → ∀ m, Array.index_usize basis j=ok m → m.val<2^31-1) :
 ∃ iter1 row,
 verifier.accumulate_batched_with_node_loop1.body (install ops)
   v q next 64#usize basis iter b=
   ok (cont (iter1,{b with raw:=b.raw.set iter.start row})) ∧
 iter1.start.val=iter.start.val+1 ∧ iter1.end=iter.end ∧
 NBB_Sweep.Inv b.terms.val (iter.start.val+1) (b.raw.set iter.start row) := by
 obtain ⟨⟨o,iter1⟩,hr,ho,hs,he⟩ := WP.spec_imp_exists
   (core.iter.range.IteratorRange.next_UScalar_some_spec
    (ty:=.Usize) (cloneInst:=core.clone.CloneUsize)
    (partialOrdInst:=core.cmp.PartialOrdUsize) (by intro x;rfl) (by intro x y;rfl)
    iter (by omega))
 subst o
 obtain ⟨m,hm,hval⟩ := WP.spec_imp_exists
   (Array.index_usize_spec basis iter.start (by rw [basis.property];change iter.start.val<256;omega))
 obtain ⟨y,hpush,hinv,frame⟩ := NBF_Read.push (Port3_RowsInstall.toBW b)
   iter.start (Port3_RowsInstall.toK q) m x inv read hq (hb iter.start active m hm)
 have push : Port3_NativeRowFrame.push b iter.start q m=
   ok {b with raw:=b.raw.set iter.start (S7Kani2OwnedRowRefinement.makeRow y)} := by
   simp only [Port3_NativeRowFrame.push,hpush,bind_tc_ok]
   rfl
 obtain ⟨word,hw,hword⟩ := WP.spec_imp_exists
   (alloc.vec.Vec.index_usize_spec v iter.start (by change iter.start.val<v.val.length;omega))
 have hw' : core.slice.index.Slice.index (core.slice.index.SliceIndexUsizeSlice Q)
   v.deref iter.start=ok word := hw
 refine ⟨iter1,S7Kani2OwnedRowRefinement.makeRow y,?_,hs,he,hinv⟩
 simp only [verifier.accumulate_batched_with_node_loop1.body,hr,install,hm,push,
   hw',lift,bind_tc_ok]
 rfl
#print axioms body
end NBF_RowInstall
