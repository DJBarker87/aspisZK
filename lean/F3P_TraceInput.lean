import AspisR1DecodeKFullValueTrace
set_option autoImplicit false
namespace AspisR1.F3P_TraceInput
open Aeneas Aeneas.Std Result AspisR1DecodeKFullValueTrace

theorem bytes (r : AspisR1DecodeKFullV10.r1_wire.ValidatedRecord)
    (byteOffset j offset : Usize) (q : QM) (t : ParserTrace r byteOffset j offset q) :
    (ParserTrace.inputBytes t).val=[(ParserTrace.b0 t),(ParserTrace.b1 t),(ParserTrace.b2 t),(ParserTrace.b3 t),(ParserTrace.b4 t),(ParserTrace.b5 t),(ParserTrace.b6 t),(ParserTrace.b7 t),
      (ParserTrace.b8 t),(ParserTrace.b9 t),(ParserTrace.b10 t),(ParserTrace.b11 t),(ParserTrace.b12 t),(ParserTrace.b13 t),(ParserTrace.b14 t),(ParserTrace.b15 t)] := by
  have same : Array.to_slice (Array.make 16#usize
    [(ParserTrace.b0 t),(ParserTrace.b1 t),(ParserTrace.b2 t),(ParserTrace.b3 t),(ParserTrace.b4 t),(ParserTrace.b5 t),(ParserTrace.b6 t),(ParserTrace.b7 t),(ParserTrace.b8 t),(ParserTrace.b9 t),(ParserTrace.b10 t),(ParserTrace.b11 t),(ParserTrace.b12 t),(ParserTrace.b13 t),(ParserTrace.b14 t),(ParserTrace.b15 t)])=(ParserTrace.inputBytes t) :=
    Result.ok.inj (ParserTrace.hinput t)
  exact (congrArg Subtype.val same).symm

#print axioms bytes
end AspisR1.F3P_TraceInput
