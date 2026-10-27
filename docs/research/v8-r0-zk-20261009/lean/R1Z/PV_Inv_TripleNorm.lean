import R1Z.PV_Inv_NativeNormQ
import R1Z.PV_Inv_NativeNormC
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_Inv_TripleNorm
open Aeneas Aeneas.Std Result AspisR1ProducerRelease47
open ProverCommitPrimitive47 ProverCommitSubfieldOps47
open AspisR1.ExtractedCurrentQM31Exact (decode)

def SafeTower (x : Old.Q) : Prop :=
  ∃ a b r n : Old.C, ∃ aa bb m : U32,
    field.CM31.square (ProverCommitNativeC49.source x.c0)=ok (ProverCommitNativeC49.source a) ∧
    field.CM31.square (ProverCommitNativeC49.source x.c1)=ok (ProverCommitNativeC49.source b) ∧
    kernels.mul_r (ProverCommitNativeC49.source b)=ok (ProverCommitNativeC49.source r) ∧
    field.CM31.sub (ProverCommitNativeC49.source a) (ProverCommitNativeC49.source r)=ok (ProverCommitNativeC49.source n) ∧
    ProverCommitNativeC49.Canonical n ∧ ProverCommitNativeC49.value n ≠ 0 ∧
    field.M31.mul n.a n.a=ok aa ∧ field.M31.mul n.b n.b=ok bb ∧
    field.M31.add aa bb=ok m ∧ ProverCommitM31Ops48.canonical m ∧ m ≠ 0#u32

theorem nonzero_tower (x : Old.Q) (hx : Canonical x) (hn : decode x ≠ 0) : SafeTower x := by
  obtain ⟨a,b,r,n,ha,hb,hr,hsub,hcn,hnn⟩ := PV_Inv_NativeNormQ.norm_operand x hx hn
  obtain ⟨aa,bb,m,haa,hbb,hm,hcm,hnm⟩ := PV_Inv_NativeNormC.norm_operand n hcn hnn
  exact ⟨a,b,r,n,aa,bb,m,ha,hb,hr,hsub,hcn,hnn,haa,hbb,hm,hcm,hnm⟩

#print axioms nonzero_tower
end R1Z.PV_Inv_TripleNorm
