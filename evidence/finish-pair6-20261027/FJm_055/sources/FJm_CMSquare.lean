import FJm_SquareAlgebra
import FJm_SquareOperand
import FIo_CMMulValues
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJm_CMSquare
open Aeneas Aeneas.Std Result AspisR1CurrentWide.Proof
open FIo_FieldBridge (NC cm)
attribute [local irreducible] QuadraticAlgebra.instInv

theorem value (x out : NC) (hx : FIo_CMValues.Canon x)
    (run : FIo_Native.aspis_core.field.CM31.square x=ok out) :
    FIo_CMValues.Canon out ∧ decodeC (cm out)=decodeC (cm x)*decodeC (cm x) := by
  obtain ⟨product,hchecked,hoperand,numeric⟩ := FJm_SquareOperand.value x.a x.b hx.1 hx.2
  change (do
    let real ← FIo_Native.aspis_core.field.M31.reduce_u64 (FJm_SquareOperand.operand x.a x.b)
    let ab ← FIo_Native.aspis_core.field.M31.mul x.a x.b
    let imag ← FIo_Native.aspis_core.field.M31.double ab
    ok (⟨real,imag⟩ : NC))=ok out at run
  rw [hoperand] at run
  obtain ⟨real,hr,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨ab,hab,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨imag,hi,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  cases Result.ok.inj run
  have vr := FIo_ReduceValues.field_value product real hr
  have cr := (FIo_ReduceValues.m31_value product real hr).2
  have vab := FIo_M31Values.mul x.a x.b ab hab
  change FIo_Native.aspis_core.field.M31.add ab ab=ok imag at hi
  have vi := FIo_M31Values.add ab ab imag vab.1 vab.1 hi
  rw [numeric,Nat.cast_mul,Nat.cast_add,
    Nat.cast_sub (by have := hx.2;omega),Nat.cast_add,ZMod.natCast_self,add_zero] at vr
  refine ⟨⟨cr,vi.1⟩,?_⟩
  apply QuadraticAlgebra.ext
  · change decodeM real=decodeM x.a*decodeM x.a+(-1)*decodeM x.b*decodeM x.b
    have realValue : decodeM real=(decodeM x.a+decodeM x.b)*(decodeM x.a-decodeM x.b) := vr
    exact realValue.trans (FJm_SquareAlgebra.real (decodeM x.a) (decodeM x.b))
  · simp only [decodeC,cm,QuadraticAlgebra.im_mul,zero_mul,zero_add,add_zero]
    rw [vi.2,vab.2]
    exact FJm_SquareAlgebra.imag (decodeM x.a) (decodeM x.b)
#print axioms value
end AspisR1.FJm_CMSquare
end
