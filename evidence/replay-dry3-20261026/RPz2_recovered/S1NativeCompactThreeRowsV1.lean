import S1NativeCompactOrdinaryPrefixV1
import CurrentCallerUsizeArithmeticV1
set_option autoImplicit false
namespace AspisS1NativeCompactThreeRows
open Aeneas Aeneas.Std Result
open AspisS1NativeCompact AspisS1NativeCompactBodyFrame AspisS1NativeCompactOrdinaryPrefix

def iter (start : U8) : core.ops.range.Range U8 := {start:=start,«end»:=compact.SEMANTIC_ROWS}

private theorem advance (x y : U8) (hlt : x.val<27) (hsucc : y.val=x.val+1) :
    core.iter.range.IteratorRange.next core.iter.range.StepU8 (iter x)=ok (some x,iter y) := by
  have within : x.val<U8.max := by scalar_tac
  simp [iter,compact.SEMANTIC_ROWS,core.iter.range.IteratorRange.next,
    core.iter.range.StepU8,core.iter.range.UScalarStep,
    core.cmp.PartialOrdU8,core.cmp.impls.PartialOrdU8.lt,
    core.clone.CloneU8,core.clone.impls.CloneU8.clone,
    liftFun1,liftFun2,core.iter.range.UScalarStep.forward_checked,hlt,within]
  first
  | exact hsucc.symm
  | exact UScalar.eq_of_val_eq hsucc.symm
  | congr 2
    apply UScalar.eq_of_val_eq
    exact hsucc.symm

private theorem advance0 : core.iter.range.IteratorRange.next core.iter.range.StepU8 (iter 0#u8)=
    ok (some 0#u8,iter 1#u8) := advance _ _ (by scalar_tac) (by scalar_tac)
private theorem advance1 : core.iter.range.IteratorRange.next core.iter.range.StepU8 (iter 1#u8)=
    ok (some 1#u8,iter 2#u8) := advance _ _ (by scalar_tac) (by scalar_tac)
private theorem advance2 : core.iter.range.IteratorRange.next core.iter.range.StepU8 (iter 2#u8)=
    ok (some 2#u8,iter 3#u8) := advance _ _ (by scalar_tac) (by scalar_tac)

private theorem add32 : (32#usize+5#usize : Result Usize)=ok 37#usize := by
  apply AspisR1CurrentCaller.UsizeArithmetic.add_eq_ok <;> scalar_tac
private theorem add37 : (37#usize+5#usize : Result Usize)=ok 42#usize := by
  apply AspisR1CurrentCaller.UsizeArithmetic.add_eq_ok <;> scalar_tac
private theorem add42 : (42#usize+5#usize : Result Usize)=ok 47#usize := by
  apply AspisR1CurrentCaller.UsizeArithmetic.add_eq_ok <;> scalar_tac
private theorem add47 : (47#usize+32#usize : Result Usize)=ok 79#usize := by
  apply AspisR1CurrentCaller.UsizeArithmetic.add_eq_ok <;> scalar_tac
private theorem addZero37 : (37#usize+0#usize : Result Usize)=ok 37#usize := by
  apply AspisR1CurrentCaller.UsizeArithmetic.add_eq_ok <;> scalar_tac
private theorem addZero42 : (42#usize+0#usize : Result Usize)=ok 42#usize := by
  apply AspisR1CurrentCaller.UsizeArithmetic.add_eq_ok <;> scalar_tac

private theorem loop_step {α β : Type} (body : α → Result (ControlFlow α β))
    (state : α) (out : β) (call : loop body state=ok out) :
    ∃ r, body state=ok r ∧
      match r with | .cont next => loop body next=ok out | .done value => value=out := by
  unfold loop at call
  cases step : body state with
  | fail error => simp only [step,bind_tc_fail] at call;cases call
  | div => simp only [step,bind_tc_div] at call;cases call
  | ok r =>
    refine ⟨r,rfl,?_⟩
    rw [step] at call
    cases r with
    | cont next => exact call
    | done value => exact Result.ok.inj call

/-- The first three actual native rows copy through logical byte 79. Every
iteration is obtained from this same accepted loop, then the already proved
native tail invariant preserves that prefix. No row-step or copy success is
an independent premise. All native value-expansion leaves remain arbitrary. -/
theorem three_rows (ops : Ops) (input out : Slice U8) (r : Exit)
    (earlier : Prefix 32 input out)
    (call : compact.expand_semantic_loop ops (iter 0#u8) input out 32#usize 32#usize=ok r) :
    Prefix 79 input r.2 := by
  let body : State → Result (ControlFlow State Exit) :=
    fun (it,buf,s,d) => compact.expand_semantic_loop.body ops input it buf s d
  change loop body (iter 0#u8,out,32#usize,32#usize)=ok r at call
  obtain ⟨r0,step0,tail0⟩ := loop_step body _ r call
  obtain ⟨out0,same0,kept0⟩ := ordinary_prefix ops input out (iter 0#u8) (iter 1#u8)
    0#u8 0#u8 0#usize 32#usize 37#usize 37#usize advance0 rfl rfl add32 addZero37 earlier r0 step0
  rw [same0] at tail0
  obtain ⟨r1,step1,tail1⟩ := loop_step body _ r tail0
  obtain ⟨out1,same1,kept1⟩ := ordinary_prefix ops input out0 (iter 1#u8) (iter 2#u8)
    1#u8 0#u8 0#usize 37#usize 42#usize 42#usize advance1 rfl rfl add37 addZero42 kept0 r1 step1
  rw [same1] at tail1
  obtain ⟨r2,step2,tail2⟩ := loop_step body _ r tail1
  obtain ⟨out2,same2,kept2⟩ := ordinary_prefix ops input out1 (iter 2#u8) (iter 3#u8)
    2#u8 1#u8 32#usize 42#usize 47#usize 79#usize advance2 rfl rfl add42 add47 kept1 r2 step2
  rw [same2] at tail2
  have tailCall : compact.expand_semantic_loop ops (iter 3#u8) input out2 79#usize 79#usize=ok r := tail2
  have preserved := loop_frame ops input out2 (iter 3#u8) 79#usize 79#usize 79
    (by scalar_tac) r tailCall
  exact fun j hj => (preserved j hj).trans (kept2 j hj)

#print axioms three_rows
end AspisS1NativeCompactThreeRows
