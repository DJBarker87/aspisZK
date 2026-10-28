import NDO_JGs_KindForward
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGs_RegularForward
open Aeneas Aeneas.Std Result
open FIo_FieldBridge (NE NQ)
/-- Compose the ordered native writes on their actual successive scratch states. -/
theorem source [FIo_Native.Allocation] (w : FIo_Native.weights.Weights)
    (alpha : Slice NE) (f : Slice U8) (folds n : Usize) (ap0 ap1 : Array NE 4#usize)
    (s0 s1 s2 s3 : alloc.vec.Vec NQ) (p0 p1 p2 p3 : Array NE 7#usize)
    (absorption : FIo_Native.weights.process_kind w 2#usize alpha f folds n ap0 ap1 s0 p0=ok (.Ok (),s1,p1))
    (circle0 : FIo_Native.weights.process_kind w 5#usize alpha f folds n ap0 ap1 s1 p1=ok (.Ok (),s2,p2))
    (circle1 : FIo_Native.weights.process_kind w 6#usize alpha f folds n ap0 ap1 s2 p2=ok (.Ok (),s3,p3)) :
    FIo_Native.weights.process_regular_kinds w true alpha f folds n ap0 ap1 s0 p0=ok (.Ok (),s3,p3) := by
  unfold FIo_Native.weights.process_regular_kinds
  simp only [ite_true,absorption,bind_tc_ok,Aeneas.Std.uncurry,
    core.result.Result.Insts.CoreOpsTry.branch,circle0,circle1]
#print axioms source
end AspisR1.JGs_RegularForward
end
