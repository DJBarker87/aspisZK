import RPu_FJj_RegularTrace
import RPu_FJj_RegularFrame
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJm_RegularContinuation
open Aeneas Aeneas.Std Result
open FIo_FieldBridge (NE NQ)

/-- The same kind2 write survives the following two circle calls. -/
theorem value [FIo_Native.Allocation] (w : FIo_Native.weights.Weights) (alpha : Slice NE)
    (f : Slice U8) (folds n : Usize) (ap0 ap1 : Array NE 4#usize)
    (scratch scratchOut : alloc.vec.Vec NQ) (before after : Array NE 7#usize)
    (run : FIo_Native.weights.process_regular_kinds w true alpha f folds n ap0 ap1 scratch before=
      ok (.Ok (),scratchOut,after)) :
    ∃ (s1 : alloc.vec.Vec NQ) (parts1 : Array NE 7#usize),
      FIo_Native.weights.process_kind w 2#usize alpha f folds n ap0 ap1 scratch before=
        ok (.Ok (),s1,parts1) ∧
      FIp_ArrayValue.value after 2=FIp_ArrayValue.value parts1 2 := by
  obtain ⟨s1,s2,p1,p2,h2,h5,h6⟩ := FJj_RegularTrace.reached w alpha f folds n ap0 ap1
    scratch scratchOut before after run
  refine ⟨s1,p1,h2,?_⟩
  rw [FJj_RegularFrame.value w 6#usize alpha f folds n ap0 ap1 s2 scratchOut p2 after h6 2 (by decide),
    FJj_RegularFrame.value w 5#usize alpha f folds n ap0 ap1 s1 s2 p1 p2 h5 2 (by decide)]
#print axioms value
end AspisR1.FJm_RegularContinuation
end
