import S1OwnedQueryWordModelV1
import S1QueryWordModelV1
set_option autoImplicit false
namespace AspisS1OwnedQueryBlock.Meaning
open Aeneas Aeneas.Std Result ControlFlow
open AspisR1QueryScanUnrolled.r0_transcript

private theorem mk (n : Nat) (h : UScalar.inBounds .Usize n) :
    UScalar.tryMk .Usize n=ok (Usize.ofNatCore n h) := by
  simp only [UScalar.tryMk,UScalar.tryMkOpt,
    dif_pos ((UScalar.check_bounds_eq_inBounds .Usize n).mpr h),Result.ofOption]
  rfl

def sampleWord (block : Array U8 32#usize) (i : Nat) : U32 :=
  queryMaskWord (blockRankWord block i)

def afterWord (i : Usize) (out : AspisS1OwnedQueryBlock.Total.Output) :
    Result (ControlFlow ((Array U32 22#usize) × Usize × Usize × Usize)
      AspisS1OwnedQueryBlock.Total.LoopOutput) := do
  if out.2.2.2 then
    ok (ControlFlow.done (out.1,out.2.1,out.2.2.1,some (out.1,out.2.1,out.2.2.1,true)))
  else
    let next ← i+1#usize
    ok (ControlFlow.cont (out.1,out.2.1,out.2.2.1,next))

/-- Exact emitted indexed-loop body, with byte/range operations discharged.
No success/interpretation hypothesis for the owned word operation is added. -/
theorem body_active (block : Array U8 32#usize) (a : Array U32 22#usize)
    (len draws i : Usize) (hi : i.val<8) :
    owned_block_loop.body block a len draws i=(do
      let out ← owned_step a len draws (sampleWord block i.val)
      afterWord i out) := by
  have active : i<8#usize := by scalar_tac
  let off : Usize := Usize.ofNatCore (4*i.val) (by scalar_tac)
  have offval : off.val=4*i.val := by simp [off]
  have mul : 4#usize*i=ok off := by change UScalar.tryMk .Usize (4*i.val)=_;exact mk _ _
  let p1 : Usize := Usize.ofNatCore (4*i.val+1) (by scalar_tac)
  let p2 : Usize := Usize.ofNatCore (4*i.val+2) (by scalar_tac)
  let p3 : Usize := Usize.ofNatCore (4*i.val+3) (by scalar_tac)
  have add1 : off+1#usize=ok p1 := by change UScalar.tryMk .Usize (off.val+1)=_;simp only [offval];exact mk _ _
  have add2 : off+2#usize=ok p2 := by change UScalar.tryMk .Usize (off.val+2)=_;simp only [offval];exact mk _ _
  have add3 : off+3#usize=ok p3 := by change UScalar.tryMk .Usize (off.val+3)=_;simp only [offval];exact mk _ _
  have index0 := AspisS1QueryArrayOperations.index_total block off (by simp [off];omega)
  have index1 := AspisS1QueryArrayOperations.index_total block p1 (by simp [p1];omega)
  have index2 := AspisS1QueryArrayOperations.index_total block p2 (by simp [p2];omega)
  have index3 := AspisS1QueryArrayOperations.index_total block p3 (by simp [p3];omega)
  have shifted : 1#u32 <<< 18#i32=ok 262144#u32 := by rfl
  have sub : 262144#u32-1#u32=ok 262143#u32 := by rfl
  let candidate := (core.num.U32.from_le_bytes (Array.make 4#usize
    [block.val[off.val]'(by have := block.property;simp [off];omega),
     block.val[p1.val]'(by have := block.property;simp [p1];omega),
     block.val[p2.val]'(by have := block.property;simp [p2];omega),
     block.val[p3.val]'(by have := block.property;simp [p3];omega)])) &&& 262143#u32
  have word : candidate=sampleWord block i.val := by
    unfold sampleWord queryMaskWord blockRankWord
    rw [dif_pos hi]
    rfl
  simp only [owned_block_loop.body,if_pos active,mul,index0,add1,index1,add2,index2,
    add3,index3,shifted,sub,bind_tc_ok,lift]
  change (do
    let (a',n,d,stop) ← owned_step a len draws candidate
    if stop then ok (ControlFlow.done (a',n,d,some (a',n,d,true)))
    else do
      let next ← i+1#usize
      ok (ControlFlow.cont (a',n,d,next))) = _
  rw [word]
  apply bind_congr
  intro out
  rcases out with ⟨a',n,d,stop⟩
  rfl

/-- One exact unfolding of the extracted tuple-state loop; no operation is
replaced and all fail/divergence branches are retained. -/
theorem loop_unroll (a : Array U32 22#usize) (len draws : Usize)
    (block : Array U8 32#usize) (i : Usize) :
    owned_block_loop a len draws block i=(do
      let cf ← owned_block_loop.body block a len draws i
      match cf with
      | .done out => ok out
      | .cont (a',n,d,j) => owned_block_loop a' n d block j) := by
  unfold owned_block_loop
  rw [loop.eq_def]
  cases h : owned_block_loop.body block a len draws i with
  | fail e => rfl
  | div => rfl
  | ok cf =>
    cases cf with
    | done out => rfl
    | cont state => rcases state with ⟨a',n,d,j⟩;rfl

#print axioms loop_unroll
#print axioms body_active
end AspisS1OwnedQueryBlock.Meaning
