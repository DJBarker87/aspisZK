import FJj_RegularTrace
import FJj_SuccessorTensor
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJj_KindTwoTrace
open Aeneas Aeneas.Std Result
open FIo_FieldBridge (NQ NE)
abbrev Vec := alloc.vec.Vec NQ
attribute [local irreducible] FIo_Native.weights.Weights.tensor
  FIo_Native.weights.Weights.scalar_factor

theorem reached [FIo_Native.Allocation] (w : FIo_Native.weights.Weights)
    (variant : w.variant=FIo_Native.transport.Variant.S2)
    (alpha : Slice NE) (f : Slice U8) (n : Usize) (ap0 ap1 : Array NE 4#usize)
    (scratch scratchOut : Vec) (before after : Array NE 7#usize)
    (run : FIo_Native.weights.process_kind w 2#usize alpha f 2#usize n ap0 ap1 scratch before=
      ok (.Ok (),scratchOut,after)) :
    ∃ (input tensor : Slice NQ) (back : Slice NQ → Vec)
      (row : Array (Array NQ 4#usize) 5#usize) (low0 low1 : Array NQ 4#usize)
      (s0 s1 scale dotValue value : NE) (dot dotOut : FIo_Native.fast_pairing.EbyKDot),
      alloc.vec.Vec.deref_mut scratch=(input,back) ∧
      FIo_Native.weights.Weights.tensor w 1#usize 2#usize input=ok tensor ∧
      Array.index_usize w.factors 1#usize=ok row ∧
      Array.index_usize row 0#usize=ok low0 ∧
      FIo_Native.weights.Weights.scalar_factor low0 ap0=ok s0 ∧
      Array.index_usize row 1#usize=ok low1 ∧
      FIo_Native.weights.Weights.scalar_factor low1 ap1=ok s1 ∧
      FIo_Native.aspis_core.field.wide_exact.WideExact.mul s0 s1=ok scale ∧
      scratchOut=back tensor ∧
      FIo_Native.fast_pairing.EbyKDot.new=ok dot ∧
      FIo_Native.weights.push_byte_products dot f (alloc.vec.Vec.deref scratchOut) n=ok (.Ok (),dotOut) ∧
      FIo_Native.fast_pairing.EbyKDot.finish dotOut=ok dotValue ∧
      FIo_Native.aspis_core.field.wide_exact.WideExact.mul scale dotValue=ok value ∧
      Array.update before 2#usize value=ok after := by
  have notD : ¬((1#isize)=(2#isize)) := by scalar_tac
  have small : (2#usize)<4#usize := by scalar_tac
  have index : Usize.wrapping_sub 2#usize 1#usize=1#usize := by scalar_tac
  unfold FIo_Native.weights.process_kind at run
  simp only [variant,FIo_Native.transport.Variant.Insts.CoreCmpPartialEqVariant.eq,
    FIo_Native.transport.Variant.read_discriminant,notD,decide_false,small,index,lift,bind_tc_ok] at run
  repeat' first | (solve | cases run) | uncase_result | head_reduce run | split at run
  cases Result.ok.inj run
  refine ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,rfl,by assumption,by assumption,by assumption,
    by assumption,by assumption,by assumption,by assumption,rfl,by assumption,?_,
    by assumption,by assumption,by assumption⟩
  have status := FJg_PairProvenance.continued _ _ (by assumption)
  subst status
  assumption
#print axioms reached
end AspisR1.FJj_KindTwoTrace
end
