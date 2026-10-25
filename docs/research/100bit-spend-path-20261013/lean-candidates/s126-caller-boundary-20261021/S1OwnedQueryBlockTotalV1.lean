import S1OwnedQueryStepTotalV1
set_option autoImplicit false
namespace AspisS1OwnedQueryBlock.Total
open Aeneas Aeneas.Std Result ControlFlow
private theorem mk (n : Nat) (h : UScalar.inBounds .Usize n) :
    UScalar.tryMk .Usize n=ok (Usize.ofNatCore n h) := by
  simp only [UScalar.tryMk,UScalar.tryMkOpt,
    dif_pos ((UScalar.check_bounds_eq_inBounds .Usize n).mpr h),Result.ofOption]
  rfl
abbrev Output := (Array U32 22#usize) × Usize × Usize × Bool
abbrev LoopOutput := (Array U32 22#usize) × Usize × Usize × Option Output
def validOutput (out : Output) : Prop := out.2.1.val≤22 ∧ out.2.2.1.val≤64
def validLoopOutput (out : LoopOutput) : Prop :=
  out.2.1.val≤22 ∧ out.2.2.1.val≤64 ∧ ∀ r,out.2.2.2=some r→validOutput r

theorem block_loop_total (fuel : Nat) (a : Array U32 22#usize) (len draws : Usize)
    (block : Array U8 32#usize) (i : Usize) (hlen : len.val≤22) (hd : draws.val≤64)
    (hi : i.val≤8) (hf : 8-i.val=fuel) :
    ∃ out, owned_block_loop a len draws block i=ok out ∧ validLoopOutput out := by
  induction fuel generalizing a len draws i with
  | zero =>
    have stop : ¬ i<8#usize := by scalar_tac
    unfold owned_block_loop
    rw [loop.eq_def]
    simp only [owned_block_loop.body,if_neg stop]
    exact ⟨(a,len,draws,none),rfl,hlen,hd,by intro r h;cases h⟩
  | succ fuel ih =>
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
    unfold owned_block_loop
    rw [loop.eq_def]
    simp only [owned_block_loop.body,if_pos active,mul,index0,add1,index1,add2,index2,
      add3,index3,shifted,sub,bind_tc_ok,lift]
    let candidate := (core.num.U32.from_le_bytes (Array.make 4#usize
      [block.val[off.val]'(by have := block.property;simp [off];omega),
       block.val[p1.val]'(by have := block.property;simp [p1];omega),
       block.val[p2.val]'(by have := block.property;simp [p2];omega),
       block.val[p3.val]'(by have := block.property;simp [p3];omega)])) &&& 262143#u32
    obtain ⟨a',len',draws',stop,call,hl',hd'⟩ := step_total a len draws candidate hlen hd
    dsimp only [candidate] at call
    rw [call]
    simp only [bind_tc_ok]
    cases stop with
    | true =>
      exact ⟨(a',len',draws',some (a',len',draws',true)),rfl,hl',hd',by
        intro r h
        cases Option.some.inj h
        exact ⟨hl',hd'⟩⟩
    | false =>
      let next : Usize := Usize.ofNatCore (i.val+1) (by scalar_tac)
      have nv : next.val=i.val+1 := by simp [next]
      have add : i+1#usize=ok next := by
        change UScalar.tryMk .Usize (i.val+1)=_
        exact mk _ _
      simp only [Bool.false_eq_true,if_false,add,bind_tc_ok]
      exact ih a' len' draws' next hl' hd' (by omega) (by omega)

/-- TOTAL extracted owned scanner on every typed block and bounded state.
Native equivalence and the full caller installation remain separate. -/
theorem block_total (a : Array U32 22#usize) (len draws : Usize)
    (block : Array U8 32#usize) (hlen : len.val≤22) (hd : draws.val≤64) :
    ∃ out, owned_block a len draws block=ok out ∧ validOutput out := by
  obtain ⟨out,call,hl,hd',pending⟩ := block_loop_total 8 a len draws block 0#usize
    hlen hd (by scalar_tac) (by scalar_tac)
  rcases out with ⟨a',len',draws',returned⟩
  unfold owned_block
  rw [call]
  cases returned with
  | none => exact ⟨(a',len',draws',false),rfl,hl,hd'⟩
  | some r => exact ⟨r,rfl,pending r rfl⟩

#print axioms block_loop_total
#print axioms block_total
end AspisS1OwnedQueryBlock.Total
