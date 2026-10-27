import SAQ_RawCM
set_option autoImplicit false
noncomputable section
namespace AspisR1.SAQ_RawQM
open Aeneas Aeneas.Std Result
open AspisR1CurrentWide AspisR1CurrentWide.Proof
abbrev Q := field.QM31

theorem add_exact (x y z : Q) (h : field.QM31.add x y=ok z) :
    decodeQM z=decodeQM x+decodeQM y := by
  unfold field.QM31.add at h
  obtain ⟨a,ha,h⟩ := Port3_PushFrame.bind_success _ _ _ h
  obtain ⟨b,hb,h⟩ := Port3_PushFrame.bind_success _ _ _ h
  have same : (⟨a,b⟩ : Q)=z := Result.ok.inj h
  subst z
  apply QuadraticAlgebra.ext
  · exact SAQ_RawCM.add_exact x.c0 y.c0 a ha
  · exact SAQ_RawCM.add_exact x.c1 y.c1 b hb

theorem mul_exact (x y z : Q) (h : field.QM31.mul x y=ok z) :
    CanonicalQM z ∧ decodeQM z=decodeQM x*decodeQM y := by
  unfold field.QM31.mul at h
  obtain ⟨ac,hac,h⟩ := Port3_PushFrame.bind_success _ _ _ h
  obtain ⟨bd,hbd,h⟩ := Port3_PushFrame.bind_success _ _ _ h
  obtain ⟨qa,hqa,h⟩ := Port3_PushFrame.bind_success _ _ _ h
  obtain ⟨qb,hqb,h⟩ := Port3_PushFrame.bind_success _ _ _ h
  obtain ⟨cross,hcross,h⟩ := Port3_PushFrame.bind_success _ _ _ h
  obtain ⟨r,hr,h⟩ := Port3_PushFrame.bind_success _ _ _ h
  obtain ⟨lo,hlo,h⟩ := Port3_PushFrame.bind_success _ _ _ h
  obtain ⟨diff,hdiff,h⟩ := Port3_PushFrame.bind_success _ _ _ h
  obtain ⟨hi,hhi,h⟩ := Port3_PushFrame.bind_success _ _ _ h
  have same : (⟨lo,hi⟩ : Q)=z := Result.ok.inj h
  subst z
  have dac := SAQ_RawCM.mul_exact x.c0 y.c0 ac hac
  have dbd := SAQ_RawCM.mul_exact x.c1 y.c1 bd hbd
  have dqa := SAQ_RawCM.add_exact x.c0 x.c1 qa hqa
  have dqb := SAQ_RawCM.add_exact y.c0 y.c1 qb hqb
  have dcross := SAQ_RawCM.mul_exact qa qb cross hcross
  have cr := SAQ_RawCM.by_r_canonical bd r dbd.1 hr
  have cl := SAQ_RawCM.add_canonical ac r lo dac.1 cr hlo
  have cd := SAQ_RawCM.sub_canonical cross ac diff dcross.1 dac.1 hdiff
  have ch := SAQ_RawCM.sub_canonical diff bd hi cd dbd.1 hhi
  refine ⟨⟨cl,ch⟩,?_⟩
  apply QuadraticAlgebra.ext
  · change decodeC lo=decodeC x.c0*decodeC y.c0+
      AspisV8R15.ExactTowerBase.qm31R*decodeC x.c1*decodeC y.c1
    rw [SAQ_RawCM.add_exact ac r lo hlo,mul_by_r_exact bd r hr,dac.2,dbd.2]
    ring
  · change decodeC hi=decodeC x.c0*decodeC y.c1+decodeC x.c1*decodeC y.c0+
      0*decodeC x.c1*decodeC y.c1
    rw [cm_sub_exact diff bd hi hhi,cm_sub_exact cross ac diff hdiff,
      dcross.2,dqa,dqb,dac.2,dbd.2]
    ring

#print axioms add_exact
#print axioms mul_exact
end AspisR1.SAQ_RawQM
end
