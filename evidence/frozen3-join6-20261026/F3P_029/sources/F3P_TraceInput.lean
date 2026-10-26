import AspisR1DecodeKFullValueTrace
set_option autoImplicit false
namespace AspisR1.F3P_TraceInput
open Aeneas Aeneas.Std Result AspisR1DecodeKFullValueTrace

theorem bytes (r : AspisR1DecodeKFullV10.r1_wire.ValidatedRecord)
    (byteOffset j offset : Usize) (q : QM) (t : ParserTrace r byteOffset j offset q) :
    (ParserTrace.inputBytes r byteOffset j offset q t).val=[(ParserTrace.b0 r byteOffset j offset q t),(ParserTrace.b1 r byteOffset j offset q t),(ParserTrace.b2 r byteOffset j offset q t),(ParserTrace.b3 r byteOffset j offset q t),(ParserTrace.b4 r byteOffset j offset q t),(ParserTrace.b5 r byteOffset j offset q t),(ParserTrace.b6 r byteOffset j offset q t),(ParserTrace.b7 r byteOffset j offset q t),
      (ParserTrace.b8 r byteOffset j offset q t),(ParserTrace.b9 r byteOffset j offset q t),(ParserTrace.b10 r byteOffset j offset q t),(ParserTrace.b11 r byteOffset j offset q t),(ParserTrace.b12 r byteOffset j offset q t),(ParserTrace.b13 r byteOffset j offset q t),(ParserTrace.b14 r byteOffset j offset q t),(ParserTrace.b15 r byteOffset j offset q t)] := by
  have same : Array.to_slice (Array.make 16#usize
    [(ParserTrace.b0 r byteOffset j offset q t),(ParserTrace.b1 r byteOffset j offset q t),(ParserTrace.b2 r byteOffset j offset q t),(ParserTrace.b3 r byteOffset j offset q t),(ParserTrace.b4 r byteOffset j offset q t),(ParserTrace.b5 r byteOffset j offset q t),(ParserTrace.b6 r byteOffset j offset q t),(ParserTrace.b7 r byteOffset j offset q t),(ParserTrace.b8 r byteOffset j offset q t),(ParserTrace.b9 r byteOffset j offset q t),(ParserTrace.b10 r byteOffset j offset q t),(ParserTrace.b11 r byteOffset j offset q t),(ParserTrace.b12 r byteOffset j offset q t),(ParserTrace.b13 r byteOffset j offset q t),(ParserTrace.b14 r byteOffset j offset q t),(ParserTrace.b15 r byteOffset j offset q t)])=(ParserTrace.inputBytes r byteOffset j offset q t) :=
    Result.ok.inj (ParserTrace.hinput r byteOffset j offset q t)
  exact (congrArg Subtype.val same).symm

#print axioms bytes
end AspisR1.F3P_TraceInput
