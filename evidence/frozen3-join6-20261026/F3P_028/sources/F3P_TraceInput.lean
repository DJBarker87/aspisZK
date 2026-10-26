import AspisR1DecodeKFullValueTrace
set_option autoImplicit false
namespace AspisR1.F3P_TraceInput
open Aeneas Aeneas.Std Result AspisR1DecodeKFullValueTrace

theorem bytes (r : AspisR1DecodeKFullV10.r1_wire.ValidatedRecord)
    (byteOffset j offset : Usize) (q : QM) (t : ParserTrace r byteOffset j offset q) :
    t.inputBytes.val=[t.b0,t.b1,t.b2,t.b3,t.b4,t.b5,t.b6,t.b7,
      t.b8,t.b9,t.b10,t.b11,t.b12,t.b13,t.b14,t.b15] := by
  have same : Array.to_slice (Array.make 16#usize
    [t.b0,t.b1,t.b2,t.b3,t.b4,t.b5,t.b6,t.b7,t.b8,t.b9,t.b10,t.b11,t.b12,t.b13,t.b14,t.b15])=t.inputBytes :=
    Result.ok.inj t.hinput
  exact (congrArg Subtype.val same).symm

#print axioms bytes
end AspisR1.F3P_TraceInput
