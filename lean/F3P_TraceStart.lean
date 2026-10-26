import F3P_TraceArithmetic
set_option autoImplicit false
namespace AspisR1.F3P_TraceStart
open Aeneas Aeneas.Std Result AspisR1DecodeKFullValueTrace

theorem start (r : AspisR1DecodeKFullV10.r1_wire.ValidatedRecord)
    (byteOffset j offset : Usize) (q : QM)
    (t : ParserTrace r byteOffset j offset q) :
    (ParserTrace.payloadStart t).val=byteOffset.val+32*j.val := by
  have stride := F3P_TraceArithmetic.checked_mul j 32#usize (ParserTrace.strideValue t) (ParserTrace.hoffsetMul t)
  have sum := F3P_TraceArithmetic.checked_add byteOffset (ParserTrace.strideValue t) (ParserTrace.payloadStart t) (ParserTrace.hstart t)
  change (ParserTrace.payloadStart t).val=byteOffset.val+32*j.val
  rw [sum]
  simpa only [show (32#usize).val=32 from rfl,Nat.mul_comm] using congrArg (byteOffset.val + ·) stride

#print axioms start
end AspisR1.F3P_TraceStart
