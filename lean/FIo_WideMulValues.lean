import FIo_WideValues
import FIo_QMMulValues
import FIo_MulUValues
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIo_WideMulValues
open Aeneas Aeneas.Std Result AspisR1CurrentWide.Proof
open FIo_FieldBridge (NE wide qm)
open FIo_WideValues (Canon)

theorem mul (x y z : NE) (hx : Canon x) (hy : Canon y)
    (run : FIo_Native.aspis_core.field.wide_exact.WideExact.mul x y=ok z) :
    Canon z ∧ decodeWide (wide z)=decodeWide (wide x)*decodeWide (wide y) := by
  unfold FIo_Native.aspis_core.field.wide_exact.WideExact.mul at run
  obtain ⟨ac,hac,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨bd,hbd,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨qa,hqa,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨qb,hqb,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨cross,hcross,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨u,hu,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨lo,hlo,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨diff,hdiff,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨hi,hhi,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  have same : (⟨lo,hi⟩ : NE)=z := Result.ok.inj run
  subst z
  have dac := FIo_QMMulValues.mul x.c0 y.c0 ac hx.1 hy.1 hac
  have dbd := FIo_QMMulValues.mul x.c1 y.c1 bd hx.2 hy.2 hbd
  have dqa := FIo_QMValues.add x.c0 x.c1 qa hx.1 hx.2 hqa
  have dqb := FIo_QMValues.add y.c0 y.c1 qb hy.1 hy.2 hqb
  have dcross := FIo_QMMulValues.mul qa qb cross dqa.1 dqb.1 hcross
  have du := FIo_MulUValues.value bd u dbd.1 hu
  have dlo := FIo_QMValues.add ac u lo dac.1 du.1 hlo
  have ddiff := FIo_QMValues.sub cross ac diff dcross.1 dac.1 hdiff
  have dhi := FIo_QMValues.sub diff bd hi ddiff.1 dbd.1 hhi
  refine ⟨⟨dlo.1,dhi.1⟩,?_⟩
  apply QuadraticAlgebra.ext
  · simp only [decodeWide,wide,QuadraticAlgebra.re_mul]
    rw [dlo.2,du.2,dac.2,dbd.2]
    ring
  · simp only [decodeWide,wide,QuadraticAlgebra.im_mul,zero_mul,zero_add,add_zero]
    rw [dhi.2,ddiff.2,dcross.2,dqa.2,dqb.2,dac.2,dbd.2]
    ring

#print axioms mul
end AspisR1.FIo_WideMulValues
end
