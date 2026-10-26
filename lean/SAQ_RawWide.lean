import SAQ_RawQM
set_option autoImplicit false
noncomputable section
namespace AspisR1.SAQ_RawWide
open Aeneas Aeneas.Std Result
open AspisR1CurrentWide AspisR1CurrentWide.Proof

theorem add_exact (x y z : E) (h : field.wide_exact.WideExact.add x y=ok z) :
    decodeWide z=decodeWide x+decodeWide y := by
  unfold field.wide_exact.WideExact.add at h
  obtain ⟨a,ha,h⟩ := Port3_PushFrame.bind_success _ _ _ h
  obtain ⟨b,hb,h⟩ := Port3_PushFrame.bind_success _ _ _ h
  have same : (⟨a,b⟩ : E)=z := Result.ok.inj h
  subst z
  apply QuadraticAlgebra.ext
  · exact SAQ_RawQM.add_exact x.c0 y.c0 a ha
  · exact SAQ_RawQM.add_exact x.c1 y.c1 b hb

theorem sub_exact (x y z : E) (h : field.wide_exact.WideExact.sub x y=ok z) :
    decodeWide z=decodeWide x-decodeWide y := by
  unfold field.wide_exact.WideExact.sub at h
  obtain ⟨a,ha,h⟩ := Port3_PushFrame.bind_success _ _ _ h
  obtain ⟨b,hb,h⟩ := Port3_PushFrame.bind_success _ _ _ h
  have same : (⟨a,b⟩ : E)=z := Result.ok.inj h
  subst z
  apply QuadraticAlgebra.ext
  · exact qm_sub_exact x.c0 y.c0 a ha
  · exact qm_sub_exact x.c1 y.c1 b hb

theorem mul_exact (x y z : E) (h : field.wide_exact.WideExact.mul x y=ok z) :
    CanonicalWide z ∧ decodeWide z=decodeWide x*decodeWide y := by
  unfold field.wide_exact.WideExact.mul at h
  obtain ⟨ac,hac,h⟩ := Port3_PushFrame.bind_success _ _ _ h
  obtain ⟨bd,hbd,h⟩ := Port3_PushFrame.bind_success _ _ _ h
  obtain ⟨qa,hqa,h⟩ := Port3_PushFrame.bind_success _ _ _ h
  obtain ⟨qb,hqb,h⟩ := Port3_PushFrame.bind_success _ _ _ h
  obtain ⟨cross,hcross,h⟩ := Port3_PushFrame.bind_success _ _ _ h
  obtain ⟨u,hu,h⟩ := Port3_PushFrame.bind_success _ _ _ h
  obtain ⟨lo,hlo,h⟩ := Port3_PushFrame.bind_success _ _ _ h
  obtain ⟨diff,hdiff,h⟩ := Port3_PushFrame.bind_success _ _ _ h
  obtain ⟨hi,hhi,h⟩ := Port3_PushFrame.bind_success _ _ _ h
  have same : (⟨lo,hi⟩ : E)=z := Result.ok.inj h
  subst z
  have dac := SAQ_RawQM.mul_exact x.c0 y.c0 ac hac
  have dbd := SAQ_RawQM.mul_exact x.c1 y.c1 bd hbd
  have dqa := SAQ_RawQM.add_exact x.c0 x.c1 qa hqa
  have dqb := SAQ_RawQM.add_exact y.c0 y.c1 qb hqb
  have dcross := SAQ_RawQM.mul_exact qa qb cross hcross
  have cu := mul_u_success_canonical bd u dbd.1 hu
  have dlo := qm_add_success ac u lo dac.1 cu hlo
  have cd := qm_sub_success_canonical cross ac diff dcross.1 dac.1 hdiff
  have ch := qm_sub_success_canonical diff bd hi cd dbd.1 hhi
  refine ⟨⟨dlo.1,ch⟩,?_⟩
  apply QuadraticAlgebra.ext
  · simp only [decodeWide,QuadraticAlgebra.re_mul]
    rw [dlo.2,mul_u_exact bd u hu,dac.2,dbd.2]
    ring
  · simp only [decodeWide,QuadraticAlgebra.im_mul,zero_mul,zero_add,add_zero]
    rw [qm_sub_exact diff bd hi hhi,qm_sub_exact cross ac diff hdiff,
      dcross.2,dqa,dqb,dac.2,dbd.2]
    ring

#print axioms add_exact
#print axioms sub_exact
#print axioms mul_exact
end AspisR1.SAQ_RawWide
end
