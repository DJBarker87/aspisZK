import FJm_CMSquareRawTrace
set_option autoImplicit false
namespace AspisR1.FJm_CMSquareOperandJoin
open Aeneas Aeneas.Std Result
open FIo_FieldBridge (NC)
open FJm_CMSquareRawTrace (widen)

theorem value (x : NC) (i1 i3 i4 i5 i6 i7 i8 i9 i10 : U64)
    (h1 : lift (widen x.a)=ok i1) (h3 : lift (widen x.b)=ok i3)
    (h4 : lift (U64.wrapping_add i1 i3)=ok i4) (h5 : lift (widen x.a)=ok i5)
    (h6 : lift (widen FIo_Native.aspis_core.field.P)=ok i6)
    (h7 : lift (U64.wrapping_add i5 i6)=ok i7) (h8 : lift (widen x.b)=ok i8)
    (h9 : lift (U64.wrapping_sub i7 i8)=ok i9) (h10 : lift (U64.wrapping_mul i4 i9)=ok i10) :
    FJm_SquareOperand.operand x.a x.b=i10 := by
  have e1 := Result.ok.inj h1
  have e3 := Result.ok.inj h3
  have e4 := Result.ok.inj h4
  have e5 := Result.ok.inj h5
  have e6 := Result.ok.inj h6
  have e7 := Result.ok.inj h7
  have e8 := Result.ok.inj h8
  have e9 := Result.ok.inj h9
  have e10 := Result.ok.inj h10
  unfold FJm_SquareOperand.operand
  rw [e1,e3,e4,e5,e6,e7,e8,e9,e10]
#print axioms value
end AspisR1.FJm_CMSquareOperandJoin
