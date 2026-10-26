import FIo_CMValues
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIo_ByRValues
open Aeneas Aeneas.Std Result AspisR1CurrentWide.Proof
open FIo_FieldBridge (NC cm)
open FIo_CMValues (Canon)

theorem value (x z : NC) (hx : Canon x)
    (run : FIo_Native.aspis_core.field.mul_by_r x=ok z) :
    Canon z ∧ decodeC (cm z)=AspisV8R15.ExactTowerBase.qm31R*decodeC (cm x) := by
  unfold FIo_Native.aspis_core.field.mul_by_r at run
  obtain ⟨m,hm,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨a,ha,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨n,hn,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨b,hb,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  have same : (⟨a,b⟩ : NC)=z := Result.ok.inj run
  subst z
  have vm := FIo_M31Values.add x.a x.a m hx.1 hx.1 hm
  have va := FIo_M31Values.sub m x.b a vm.1 hx.2 ha
  have vn := FIo_M31Values.add x.b x.b n hx.2 hx.2 hn
  have vb := FIo_M31Values.add x.a n b hx.1 vn.1 hb
  refine ⟨⟨va.1,vb.1⟩,?_⟩
  apply QuadraticAlgebra.ext
  · change decodeM a=2*decodeM x.a+(-1)*decodeM x.b
    rw [va.2,vm.2]
    ring
  · simp only [decodeC,cm,AspisV8R15.ExactTowerBase.qm31R,QuadraticAlgebra.im_mul,zero_mul,zero_add,add_zero,one_mul]
    rw [vb.2,vn.2]
    ring

#print axioms value
end AspisR1.FIo_ByRValues
end
