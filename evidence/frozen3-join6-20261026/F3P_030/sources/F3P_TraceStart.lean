import F3P_TraceArithmetic
set_option autoImplicit false
namespace AspisR1.F3P_TraceStart
open Aeneas Aeneas.Std Result AspisR1DecodeKFullValueTrace

theorem start (r : AspisR1DecodeKFullV10.r1_wire.ValidatedRecord)
    (byteOffset j offset : Usize) (q : QM)
    (t : ParserTrace r byteOffset j offset q) :
    (ParserTrace.payloadStart r byteOffset j offset q t).val=byteOffset.val+32*j.val := by
  have stride := F3P_TraceArithmetic.checked_mul j 32#usize (ParserTrace.strideValue r byteOffset j offset q t) (ParserTrace.hoffsetMul r byteOffset j offset q t)
  have sum := F3P_TraceArithmetic.checked_add byteOffset (ParserTrace.strideValue r byteOffset j offset q t) (ParserTrace.payloadStart r byteOffset j offset q t) (ParserTrace.hstart r byteOffset j offset q t)
  change (ParserTrace.payloadStart r byteOffset j offset q t).val=byteOffset.val+32*j.val
  rw [sum,stride]
  omega

#print axioms start
end AspisR1.F3P_TraceStart
