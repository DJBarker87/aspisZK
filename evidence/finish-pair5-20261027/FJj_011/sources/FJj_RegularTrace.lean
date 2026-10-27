import FJg_PairProvenance
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJj_RegularTrace
open Aeneas Aeneas.Std Result
open FIo_FieldBridge (NE NQ)
abbrev Vec := alloc.vec.Vec NQ

theorem reached (w : FIo_Native.weights.Weights) (alpha : Slice NE) (f : Slice U8)
    (folds n : Usize) (ap0 ap1 : Array NE 4#usize)
    (scratch scratchOut : Vec) (before after : Array NE 7#usize)
    (run : FIo_Native.weights.process_regular_kinds w true alpha f folds n ap0 ap1 scratch before=
      ok (.Ok (),scratchOut,after)) :
    ∃ (scratch1 scratch2 : Vec) (parts1 parts2 : Array NE 7#usize),
      FIo_Native.weights.process_kind w 2#usize alpha f folds n ap0 ap1 scratch before=
        ok (.Ok (),scratch1,parts1) ∧
      FIo_Native.weights.process_kind w 5#usize alpha f folds n ap0 ap1 scratch1 parts1=
        ok (.Ok (),scratch2,parts2) ∧
      FIo_Native.weights.process_kind w 6#usize alpha f folds n ap0 ap1 scratch2 parts2=
        ok (.Ok (),scratchOut,after) := by
  unfold FIo_Native.weights.process_regular_kinds at run
  simp only [ite_true] at run
  repeat' first
  | (solve | cases run)
  | uncase_result
  | head_reduce run
  | split at run
  cases Result.ok.inj run
  refine ⟨_,_,_,_,?_,?_,?_⟩ <;> assumption
#print axioms reached
end AspisR1.FJj_RegularTrace
end
