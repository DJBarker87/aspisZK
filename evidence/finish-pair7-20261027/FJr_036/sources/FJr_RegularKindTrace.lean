import FJj_RegularTrace
import FJj_KindScaleTrace
import FJj_SuccessorTensor
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJr_RegularKindTrace
open Aeneas Aeneas.Std Result
open FIo_FieldBridge (NQ NE)
abbrev Vec := alloc.vec.Vec NQ
attribute [local irreducible] FIo_Native.weights.Weights.tensor
  FIo_Native.weights.Weights.scalar_factor FIo_Native.fast_pairing.EbyKDot.new

theorem reached [FIo_Native.Allocation] (w : FIo_Native.weights.Weights)
    (variant : w.variant=FIo_Native.transport.Variant.S2)
    (kind idx : Usize) (large : ¬kind < 4#usize)
    (index : Usize.wrapping_sub kind 2#usize=idx)
    (alpha : Slice NE) (f : Slice U8) (n : Usize) (ap0 ap1 : Array NE 4#usize)
    (scratch scratchOut : Vec) (before after : Array NE 7#usize)
    (run : FIo_Native.weights.process_kind w kind alpha f 2#usize n ap0 ap1 scratch before=
      ok (.Ok (),scratchOut,after)) :
    ∃ (input tensor : Slice NQ) (back : Slice NQ → Vec)
      (row : Array (Array NQ 4#usize) 5#usize) (low0 low1 : Array NQ 4#usize)
      (s0 s1 scale dotValue value : NE) (dot dotOut : FIo_Native.fast_pairing.EbyKDot),
      alloc.vec.Vec.deref_mut scratch=(input,back) ∧
      FIo_Native.weights.Weights.tensor w idx 2#usize input=ok tensor ∧
      Array.index_usize w.factors idx=ok row ∧
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
      Array.update before kind value=ok after := by
  have notD : ¬((1#isize)=(2#isize)) := by scalar_tac
  unfold FIo_Native.weights.process_kind at run
  simp only [variant,FIo_Native.transport.Variant.Insts.CoreCmpPartialEqVariant.eq,
    FIo_Native.transport.Variant.read_discriminant,notD,decide_false,large,index,lift,bind_tc_ok] at run
  repeat' first | (solve | contradiction) | (solve | cases run) | uncase_result | head_reduce run | split at run
  simp only [ite_true] at *
  rename_i hFalse tensorResult tensor tensorRun rowResult row rowRun lowResult low0 lowRun
    scalarResult s0 scalarRun tupleResult tuple dotResult dot dotRun pushResult pushed
    pushRun flowResult flow unit branchRun finishResult dotValue finishRun
    valueResult value valueRun writeResult written writeRun tupleRun
  have tupleCut := FJj_KindScaleTrace.reached row ap1 s0 tensor
    (fun t => (alloc.vec.Vec.deref_mut scratch).2 t) tuple.1 tuple.2 tupleRun
  obtain ⟨low1,s1,read1,scalar1,mulScale,backEq⟩ := tupleCut
  have normal := FJj_KindScaleTrace.ok_pair pushed unit branchRun
  have pushOk := pushRun.trans (congrArg Result.ok normal)
  cases Result.ok.inj run
  exact ⟨(alloc.vec.Vec.deref_mut scratch).1,tensor,(alloc.vec.Vec.deref_mut scratch).2,
    row,low0,low1,s0,s1,tuple.2,dotValue,value,dot,pushed.2,rfl,
    tensorRun,rowRun,lowRun,scalarRun,read1,scalar1,mulScale,backEq,dotRun,
    pushOk,finishRun,valueRun,writeRun⟩
#print axioms reached
end AspisR1.FJr_RegularKindTrace
end
