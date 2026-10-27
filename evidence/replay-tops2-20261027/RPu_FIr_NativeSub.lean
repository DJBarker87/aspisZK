import RPu_FIr_NativeValue
import RPu_FIr_NativeScalar
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIr_NativeSub
open Aeneas Aeneas.Std Result
open FIr_NativeArithmetic
open FIr_NativeValue (Canon decode K)
def CanonC (x : NC) : Prop := x.a.val<2147483647 ∧ x.b.val<2147483647
def decodeC (x : NC) : AspisV8R15.ExactTowerBase.CM31Exact :=
  ⟨(x.a.val : AspisV8R15.ExactTowerBase.M31Exact),(x.b.val : AspisV8R15.ExactTowerBase.M31Exact)⟩

theorem cm (x y z : NC) (hx : CanonC x) (hy : CanonC y)
    (run : FIq_Native.field.CM31.sub x y=ok z) :
    CanonC z ∧ decodeC z=decodeC x-decodeC y := by
  unfold FIq_Native.field.CM31.sub at run
  obtain ⟨a,ha,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨b,hb,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  have same : (⟨a,b⟩ : NC)=z := Result.ok.inj run
  subst z
  have va := FIr_NativeScalar.sub x.a y.a a hx.1 hy.1 ha
  have vb := FIr_NativeScalar.sub x.b y.b b hx.2 hy.2 hb
  refine ⟨⟨va.1,vb.1⟩,?_⟩
  apply QuadraticAlgebra.ext
  · exact va.2
  · exact vb.2

theorem qm (x y z : NQ) (hx : Canon x) (hy : Canon y)
    (run : FIq_Native.field.QM31.sub x y=ok z) :
    Canon z ∧ decode z=decode x-decode y := by
  unfold FIq_Native.field.QM31.sub at run
  obtain ⟨a,ha,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨b,hb,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  have same : (⟨a,b⟩ : NQ)=z := Result.ok.inj run
  subst z
  have va := cm x.c0 y.c0 a hx.1 hy.1 ha
  have vb := cm x.c1 y.c1 b hx.2 hy.2 hb
  refine ⟨⟨va.1,vb.1⟩,?_⟩
  apply QuadraticAlgebra.ext
  · exact va.2
  · exact vb.2

#print axioms cm
#print axioms qm
end AspisR1.FIr_NativeSub
end
