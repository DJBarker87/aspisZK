import FJj_RegularFrame
import FJg_SharedHighTrace
import FJf_ArraySlots
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJm_RawFrames
open Aeneas Aeneas.Std Result
open FIo_FieldBridge (NE NQ)
attribute [local irreducible] FIo_Native.weights.Weights.dense_point_pair
  FIo_Native.weights.Weights.tensor FIo_Native.weights.Weights.scalar_factor

theorem regular [FIo_Native.Allocation] (w : FIo_Native.weights.Weights) (kind : Usize)
    (alpha : Slice NE) (f : Slice U8) (folds n : Usize) (ap0 ap1 : Array NE 4#usize)
    (scratch scratchOut : alloc.vec.Vec NQ) (before after : Array NE 7#usize)
    (run : FIo_Native.weights.process_kind w kind alpha f folds n ap0 ap1 scratch before=
      ok (.Ok (),scratchOut,after)) (j : Nat) (ne : kind.val≠j) : after.val[j]?=before.val[j]? := by
  unfold FIo_Native.weights.process_kind at run
  repeat' first | (solve | cases run) | uncase_result | head_reduce run | split at run
  all_goals
    cases Result.ok.inj run
    rw [FJf_ArraySlots.update_slot before _ kind _ (by assumption) j,if_neg ne]

theorem shared (w : FIo_Native.weights.Weights) (partials ap0 ap1 : Array NE 4#usize)
    (before after : Array NE 7#usize)
    (run : FIo_Native.weights.shared_high partials w ap0 ap1 before=ok (.Ok (),after))
    (j : Nat) (h1 : (1#usize).val≠j) (h3 : (3#usize).val≠j) : after.val[j]?=before.val[j]? := by
  obtain ⟨row,coeff,low0,low1,high,s0,s1,scale,value,old,absorption,back,
    hr,h4,hh,h0,hs0,h1r,hs1,hm,hv,hb,hu⟩ := FJg_SharedHighTrace.reached w partials ap0 ap1 before after run
  rw [FJf_ArraySlots.update_slot (back value) after 3#usize absorption hu j,if_neg h3,
    FIp_ArraySetValue.back before 1#usize old back hb,FJf_ArrayOps.set_val,List.getElem?_set_ne h1]
#print axioms regular
#print axioms shared
end AspisR1.FJm_RawFrames
end
