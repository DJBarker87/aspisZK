import FIo_QMValues
import FIo_CMMulValues
import FIo_ByRValues
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIo_QMMulValues
open Aeneas Aeneas.Std Result AspisR1CurrentWide.Proof
open FIo_FieldBridge (NQ qm cm)
open FIo_QMValues (Canon)

theorem mul (x y z : NQ) (hx : Canon x) (hy : Canon y)
    (run : FIo_Native.aspis_core.field.QM31.mul x y=ok z) :
    Canon z ∧ decodeQM (qm z)=decodeQM (qm x)*decodeQM (qm y) := by
  unfold FIo_Native.aspis_core.field.QM31.mul at run
  obtain ⟨ac,hac,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨bd,hbd,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨qa,hqa,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨qb,hqb,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨cross,hcross,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨r,hr,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨lo,hlo,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨diff,hdiff,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨hi,hhi,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  have same : (⟨lo,hi⟩ : NQ)=z := Result.ok.inj run
  subst z
  have dac := FIo_CMMulValues.mul x.c0 y.c0 ac hx.1 hy.1 hac
  have dbd := FIo_CMMulValues.mul x.c1 y.c1 bd hx.2 hy.2 hbd
  have dqa := FIo_CMValues.add x.c0 x.c1 qa hx.1 hx.2 hqa
  have dqb := FIo_CMValues.add y.c0 y.c1 qb hy.1 hy.2 hqb
  have dcross := FIo_CMMulValues.mul qa qb cross dqa.1 dqb.1 hcross
  have dr := FIo_ByRValues.value bd r dbd.1 hr
  have dlo := FIo_CMValues.add ac r lo dac.1 dr.1 hlo
  have ddiff := FIo_CMValues.sub cross ac diff dcross.1 dac.1 hdiff
  have dhi := FIo_CMValues.sub diff bd hi ddiff.1 dbd.1 hhi
  refine ⟨⟨dlo.1,dhi.1⟩,?_⟩
  apply QuadraticAlgebra.ext
  · change decodeC (cm lo)=decodeC (cm x.c0)*decodeC (cm y.c0)+
      AspisV8R15.ExactTowerBase.qm31R*decodeC (cm x.c1)*decodeC (cm y.c1)
    rw [dlo.2,dr.2,dac.2,dbd.2]
    ring
  · change decodeC (cm hi)=decodeC (cm x.c0)*decodeC (cm y.c1)+
      decodeC (cm x.c1)*decodeC (cm y.c0)+0*decodeC (cm x.c1)*decodeC (cm y.c1)
    rw [dhi.2,ddiff.2,dcross.2,dqa.2,dqb.2,dac.2,dbd.2]
    ring

#print axioms mul
end AspisR1.FIo_QMMulValues
end
