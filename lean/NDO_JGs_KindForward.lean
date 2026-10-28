import NDO_JGq_PairShape
import RPv_FJj_KindScaleTrace
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGs_KindForward
open Aeneas Aeneas.Std Result
open FIo_FieldBridge (NE NQ)
/-- Forward source composition; all children are on this single scratch state. -/
theorem source [FIo_Native.Allocation] (w : FIo_Native.weights.Weights)
    (variant : w.variant=FIo_Native.transport.Variant.S2)
    (kind idx : Usize) (index : (if kind < 4#usize then Usize.wrapping_sub kind 1#usize else Usize.wrapping_sub kind 2#usize)=idx)
    (alpha : Slice NE) (f : Slice U8) (n : Usize) (ap0 ap1 : Array NE 4#usize)
    (scratch : alloc.vec.Vec NQ) (input tensor : Slice NQ) (back : Slice NQ → alloc.vec.Vec NQ)
    (borrow : alloc.vec.Vec.deref_mut scratch=(input,back))
    (row : Array (Array NQ 4#usize) 5#usize) (low0 low1 : Array NQ 4#usize)
    (s0 s1 scale dotValue value : NE) (dot dotOut : FIo_Native.fast_pairing.EbyKDot)
    (before after : Array NE 7#usize)
    (tensorRun : FIo_Native.weights.Weights.tensor w idx 2#usize input=ok tensor)
    (rowRun : Array.index_usize w.factors idx=ok row)
    (lowRun0 : Array.index_usize row 0#usize=ok low0)
    (scalar0 : FIo_Native.weights.Weights.scalar_factor low0 ap0=ok s0)
    (lowRun1 : Array.index_usize row 1#usize=ok low1)
    (scalar1 : FIo_Native.weights.Weights.scalar_factor low1 ap1=ok s1)
    (multiply : FIo_Native.aspis_core.field.wide_exact.WideExact.mul s0 s1=ok scale)
    (new : FIo_Native.fast_pairing.EbyKDot.new=ok dot)
    (push : FIo_Native.weights.push_byte_products dot f (alloc.vec.Vec.deref (back tensor)) n=ok (.Ok (),dotOut))
    (finish : FIo_Native.fast_pairing.EbyKDot.finish dotOut=ok dotValue)
    (scaled : FIo_Native.aspis_core.field.wide_exact.WideExact.mul scale dotValue=ok value)
    (write : Array.update before kind value=ok after) :
    FIo_Native.weights.process_kind w kind alpha f 2#usize n ap0 ap1 scratch before=
      ok (.Ok (),back tensor,after) := by
  have notD : ¬((1#isize)=(2#isize)) := by scalar_tac
  have indexRun : (if kind < 4#usize then ok (Usize.wrapping_sub kind 1#usize) else ok (Usize.wrapping_sub kind 2#usize) : Result Usize)=ok idx := by
    by_cases h : kind < 4#usize
    · simpa only [h,ite_true] using congrArg (fun i=> (ok i : Result Usize)) index
    · simpa only [h,ite_false] using congrArg (fun i=> (ok i : Result Usize)) index
  unfold FIo_Native.weights.process_kind
  simp only [variant,FIo_Native.transport.Variant.Insts.CoreCmpPartialEqVariant.eq,
    FIo_Native.transport.Variant.read_discriminant,notD,decide_false,Bool.false_eq_true,ite_false,indexRun,lift,bind_tc_ok,borrow,ite_true]
  simp only [Aeneas.Std.uncurry,tensorRun,bind_tc_ok,rowRun,lowRun0,scalar0,lowRun1,
    scalar1,multiply,new,push,core.result.Result.Insts.CoreOpsTry.branch,finish,scaled,write]
#print axioms source
end AspisR1.JGs_KindForward
end
