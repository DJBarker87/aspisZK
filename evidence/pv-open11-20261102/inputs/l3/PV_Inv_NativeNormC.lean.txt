import R1Z.PV_Inv_NativeQ
set_option autoImplicit false
namespace R1Z.PV_Inv_NativeNormC
open Aeneas Aeneas.Std Result AspisR1ProducerRelease47
open ProverCommitPrimitive47 ProverCommitNativeC49
open AspisV8R15.ExactTowerBase

theorem norm_operand (x : Old.C) (hx : Canonical x) (hn : value x ≠ 0) :
    ∃ aa bb n : U32,
      field.M31.mul x.a x.a = ok aa ∧ field.M31.mul x.b x.b = ok bb ∧
      field.M31.add aa bb = ok n ∧ ProverCommitM31Ops48.canonical n ∧ n ≠ 0#u32 := by
  obtain ⟨aa,haa,hcaa,hvaa⟩ := ProverCommitM31Ops48.mul_exact x.a x.a
  obtain ⟨bb,hbb,hcbb,hvbb⟩ := ProverCommitM31Ops48.mul_exact x.b x.b
  obtain ⟨n,hnn,hcn,hvn⟩ := ProverCommitM31Ops48.add_exact aa bb hcaa hcbb
  refine ⟨aa,bb,n,haa,hbb,hnn,hcn,?_⟩
  have hnorm : ProverCommitM31Ops48.decode n = QuadraticAlgebra.norm (value x) := by
    rw [hvn,hvaa,hvbb,ProverCommitNativeCInverse49.norm_value]
    rfl
  intro hz
  have hzero : ProverCommitM31Ops48.decode n = 0 := by rw [hz]; rfl
  exact hn (QuadraticAlgebra.norm_eq_zero_iff_eq_zero.mp (hnorm.symm.trans hzero))

#print axioms norm_operand
end R1Z.PV_Inv_NativeNormC
