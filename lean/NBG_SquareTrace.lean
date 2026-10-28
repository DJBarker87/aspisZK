import NBG_SquareLoop
set_option autoImplicit false
noncomputable section
namespace NBG_SquareTrace
open Aeneas Aeneas.Std Result ControlFlow AspisR1
open AspisR1M31Inverse.SquareProof

/-- Native cells supply only the paired scalar natural-value relation, not a
model return or a whole-function output equality. K028 constructs each step. -/
inductive Trace : Nat → U32 → U32 → Prop
  | done (value : U32) : Trace 0 value value
  | step {n : Nat} {before middle after : U32}
      (cell : middle.val = (before.val*before.val)%2147483647)
      (tail : Trace n middle after) : Trace (n+1) before after

theorem loop_result {n : Nat} {before after : U32}
    (trace : Trace n before after) (iter : core.ops.range.Range Usize)
    (count : iter.end.val-iter.start.val=n) :
    AspisR1M31Inverse.field.square_n_loop FIo_Native.aspis_core.field.M31.mul
      iter before = ok after := by
  induction trace generalizing iter with
  | done value =>
    have stopped : iter.start.val ≥ iter.end.val := by omega
    have next := AspisR1M31Inverse.SquareProof.next_done iter stopped
    unfold AspisR1M31Inverse.field.square_n_loop
    rw [loop.eq_def]
    simp only [AspisR1M31Inverse.field.square_n_loop.body,next,bind_tc_ok]
    rfl
  | @step n before middle after cell tail ih =>
    have active : iter.start.val < iter.end.val := by omega
    obtain ⟨rest,next,inc,last,_⟩ := AspisR1M31Inverse.SquareProof.next_step iter active
    have remaining : rest.end.val-rest.start.val=n := by rw [last,inc]; omega
    obtain ⟨word,run,value,_⟩ := LPf_BaseMultiply.source before before
    have same : word=middle := UScalar.eq_of_val_eq (value.trans cell.symm)
    rw [same] at run
    unfold AspisR1M31Inverse.field.square_n_loop
    rw [loop.eq_def]
    simp only [AspisR1M31Inverse.field.square_n_loop.body,next,run,bind_tc_ok]
    exact ih rest remaining

/-- Exact raw scalar Result for the SAME native loop trace, including count0. -/
theorem native_result (count : Usize) (before after : U32)
    (trace : Trace count.val before after) :
    AspisR1M31Inverse.field.square_n FIo_Native.aspis_core.field.M31.mul before count =
      ok after := by
  apply loop_result trace {start:=0#usize,«end»:=count}
  simp only [UScalar.ofNatCore_val_eq,Nat.sub_zero]

#print axioms loop_result
#print axioms native_result
end NBG_SquareTrace
