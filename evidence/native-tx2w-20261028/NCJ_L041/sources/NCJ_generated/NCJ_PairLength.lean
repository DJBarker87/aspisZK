import NCJ_CallLog
set_option autoImplicit false
noncomputable section
namespace NCJ_PairLength
open Aeneas Aeneas.Std Result ControlFlow FIo_Native

theorem first : weights.Weights.pair_loop0.body
    {start:=0#usize,«end»:=2#usize} 1024#usize=
      ok (cont ({start:=1#usize,«end»:=2#usize},256#usize)) := by rfl

theorem second : weights.Weights.pair_loop0.body
    {start:=1#usize,«end»:=2#usize} 256#usize=
      ok (cont ({start:=2#usize,«end»:=2#usize},64#usize)) := by rfl

theorem stop : weights.Weights.pair_loop0.body
    {start:=2#usize,«end»:=2#usize} 64#usize=ok (done 64#usize) := by rfl

/-- A two-step scalar guard only, not a tensor/group/buffer normalization. -/
theorem two_folds : weights.Weights.pair_loop0
    {start:=0#usize,«end»:=2#usize} 1024#usize=ok 64#usize := by
  unfold weights.Weights.pair_loop0
  rw [loop.eq_def]
  simp only [first,bind_tc_ok]
  rw [loop.eq_def]
  simp only [second,bind_tc_ok]
  rw [loop.eq_def]
  simp only [stop,bind_tc_ok]

variable [FIo_Native.Allocation]
theorem reject (w : weights.Weights)
    (alpha : Slice aspis_core.field.wide_exact.WideExact) (f : Slice U8)
    (kappa : aspis_core.field.wide_exact.WideExact)
    (ha : alpha.val.length=2) (hf : f.val.length=32) :
    weights.Weights.pair w alpha f kappa=ok (.Err verifier.Error.Parse) := by
  have hAlpha : Slice.len alpha=2#usize := by apply UScalar.eq_of_val_eq;exact ha
  have hFinal : Slice.len f=32#usize := by apply UScalar.eq_of_val_eq;exact hf
  simp only [weights.Weights.pair,hAlpha,hFinal,two_folds,
    show (32#usize / 32#usize)=ok 1#usize from rfl,bind_tc_ok]
  rfl

#print axioms first
#print axioms second
#print axioms stop
#print axioms two_folds
#print axioms reject
end NCJ_PairLength
