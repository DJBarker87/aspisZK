import XRn_Join_Funs
import XRk_ResultTools
import CurrentCallerUsizeArithmeticV1
open Aeneas Aeneas.Std Result XRn_Join_Release XRk_ResultTools
set_option autoImplicit false
namespace XRr_Initial64
/-- Small source shape calculation precedes any vector normalization. -/
theorem width : transport.Variant.final_len .S2=ok 64#usize := by
 have hf : transport.Variant.folds .S2=ok 2#usize := by
   unfold transport.Variant.folds
   have he : transport.Variant.Insts.CoreCmpPartialEqVariant.eq .S2 .S1=ok false := by
     change ok (decide (1#isize=0#isize))=ok false
     congr 1
     exact decide_eq_false (by scalar_tac)
   rw [he,bind_tc_ok]
   rfl
 have hm : (2#usize*2#usize : Result Usize)=ok 4#usize := by
   apply AspisR1CurrentCaller.UsizeArithmetic.mul_eq_ok <;> scalar_tac
 unfold transport.Variant.final_len
 rw [hf,bind_tc_ok,hm,bind_tc_ok]
 change UScalar.shiftRight (1024#usize) 4=ok 64#usize
 unfold UScalar.shiftRight
 rw [if_pos (by
   change 4<System.Platform.numBits
   have lower := System.Platform.le_numBits
   omega)]
 congr 1
/-- This kit's allocator model always succeeds; native reservation is separate. -/
theorem filled {T : Type} (copy : core.marker.Copy T) (n : Usize) (value : T)
 (v : alloc.vec.Vec T)
 (run : aspis_core.r0.heap.filled copy n value=ok (.Ok v)) : v.val.length=n.val := by
 unfold aspis_core.r0.heap.filled at run
 rw [dif_pos (by scalar_tac)] at run
 have same := core.result.Result.Ok.inj (Result.ok.inj run)
 subst v
 exact List.length_replicate
/-- Length 64 is derived from this initialization, not an independent run. -/
theorem init (a : verifier.Accumulator)
 (run : verifier.Accumulator.new .S2=ok (.Ok a)) : a.weights.val.length=64 ∧ a.next=0#usize := by
 unfold verifier.Accumulator.new at run
 rw [width,bind_tc_ok] at run
 obtain ⟨zero,_,run⟩ := bind_success _ _ _ run
 obtain ⟨r,hr,run⟩ := bind_success _ _ _ run
 cases r with
 | Err e =>
   simp [core.result.Result.map_err,
     verifier.Accumulator.new.closure.Insts.CoreOpsFunctionFnOnceTupleErrorError.call_once,
     core.result.Result.Insts.CoreOpsTry.branch,
     core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
     core.convert.FromSame.from] at run
 | Ok weights =>
   have hw := filled _ 64#usize zero weights hr
   simp only [core.result.Result.map_err,bind_tc_ok,
     core.result.Result.Insts.CoreOpsTry.branch] at run
   obtain ⟨wide,_,run⟩ := bind_success _ _ _ run
   obtain ⟨one,_,run⟩ := bind_success _ _ _ run
   cases core.result.Result.Ok.inj (Result.ok.inj run)
   exact ⟨hw,rfl⟩
#print axioms width
#print axioms filled
#print axioms init
end XRr_Initial64
