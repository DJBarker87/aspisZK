import FJm_RawFrames
import FJj_RegularTrace
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJm_LibraInitialSlot
open Aeneas Aeneas.Std Result
open FIo_FieldBridge (NE NQ)

theorem value [FIo_Native.Allocation] (w : FIo_Native.weights.Weights) (alpha : Slice NE)
    (f : Slice U8) (folds n : Usize) (ap0 ap1 partials : Array NE 4#usize)
    (scratch scratchOut : alloc.vec.Vec NQ) (before highParts lowParts : Array NE 7#usize) (inactive : NE)
    (regular : FIo_Native.weights.process_regular_kinds w true alpha f folds n ap0 ap1 scratch
      (Array.repeat 7#usize FIo_Native.aspis_core.field.wide_exact.WideExact.ZERO)=ok (.Ok (),scratchOut,before))
    (shared : FIo_Native.weights.shared_high partials w ap0 ap1 before=ok (.Ok (),highParts))
    (update : Array.update highParts 0#usize inactive=ok lowParts) :
    lowParts.val[4]?=some FIo_Native.aspis_core.field.wide_exact.WideExact.ZERO := by
  obtain ⟨s1,s2,p1,p2,h2,h5,h6⟩ := FJj_RegularTrace.reached w alpha f folds n ap0 ap1 scratch scratchOut _ before regular
  rw [FJf_ArraySlots.update_slot highParts lowParts 0#usize inactive update 4,if_neg (by decide),
    FJm_RawFrames.shared w partials ap0 ap1 before highParts shared 4 (by decide) (by decide),
    FJm_RawFrames.regular w 6#usize alpha f folds n ap0 ap1 s2 scratchOut p2 before h6 4 (by decide),
    FJm_RawFrames.regular w 5#usize alpha f folds n ap0 ap1 s1 s2 p1 p2 h5 4 (by decide),
    FJm_RawFrames.regular w 2#usize alpha f folds n ap0 ap1 scratch s1 _ p1 h2 4 (by decide)]
  simp only [Array.repeat,List.getElem?_replicate,show (7#usize).val=7 from by decide,
    show (4:Nat)<7 from by decide,if_true]
#print axioms value
end AspisR1.FJm_LibraInitialSlot
end
