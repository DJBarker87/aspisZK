import R1Z.ProverRwSuccessScalarInverseExact
import R1Z.ProverRwSuccessInverseTotal
import R1Z.ProverCommitNativeCInverse49
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRwSuccessComplexInverseExact
open Aeneas Aeneas.Std Result AspisR1ProducerRelease47
open ProverCommitPrimitive47 ProverCommitNativeC49
open AspisV8R15.ExactTowerBase
variable [ProverRwFull.ExternalTypes]
abbrev input (x : Old.C) : ProverRwDictionaryTower.C :=
  ProverRwDictionaryTower.fromC (source x)
theorem inverse (ops : ProverRwFull.ExternalFuns) (x : Old.C) (hx : Canonical x) (hn : value x≠0) :
    ∃ z : Old.C, ProverRwSuccessInverseTotal.Src.cInv (input x)=ok (some (input z)) ∧
      Canonical z ∧ value z=(value x)⁻¹ := by
  obtain ⟨aa,haa,hcaa,hvaa⟩ := ProverCommitM31Ops48.mul_exact x.a x.a
  obtain ⟨bb,hbb,hcbb,hvbb⟩ := ProverCommitM31Ops48.mul_exact x.b x.b
  obtain ⟨n,hnn,hcn,hvn⟩ := ProverCommitM31Ops48.add_exact aa bb hcaa hcbb
  have hnorm : ProverCommitM31Ops48.decode n=QuadraticAlgebra.norm (value x) := by
    rw [hvn,hvaa,hvbb,ProverCommitNativeCInverse49.norm_value];rfl
  have nonzero : n≠0#u32 := by
    intro hz
    have h0 : ProverCommitM31Ops48.decode n=0 := by rw [hz];rfl
    apply hn
    apply QuadraticAlgebra.norm_eq_zero_iff_eq_zero.mp
    rw [←hnorm,h0]
  let ni := ProverCommitInverse48.inverseWord n
  have hni : ProverRwSuccessInverseInstall.Src.mInv n=.ok (some ni) :=
    ProverRwSuccessScalarInverseExact.fixed_chain ops n nonzero
  unfold ProverRwSuccessInverseInstall.Src.mInv at hni
  have hcni := ProverCommitInverse48.inverse_canonical n
  have hvni := ProverCommitInverse48.inverse_decode n
  obtain ⟨a,ha,hca,hva⟩ := ProverCommitM31Ops48.mul_exact x.a ni
  obtain ⟨nb,hnb,hcnb,hvnb⟩ := ProverCommitNativeNeg49.neg_word x.b hx.2
  obtain ⟨b,hb,hcb,hvb⟩ := ProverCommitM31Ops48.mul_exact nb ni
  refine ⟨⟨a,b⟩,?_,⟨hca,hcb⟩,?_⟩
  · simp only [ProverRwSuccessInverseTotal.Src.cInv,
      ProverRwSuccessInverseSource.field.CM31.Insts.Aspis_r1_encoder53ScalarCodeField.try_inv,
      input,ProverRwDictionaryTower.fromC,source,ProverCommitRelease47.convC,fromC,
      ProverRwSuccessInverseSource.field.M31.mul,
      ProverRwSuccessInverseSource.field.M31.add,
      ProverRwSuccessInverseSource.field.M31.neg,
      haa,hbb,hnn,hni,ha,hnb,hb,bind_tc_ok,
      ProverRwDictionaryOptionSource.core.option.Option.Insts.CoreOpsTry_traitTry.branch]
  · have hvi : ProverCommitM31Ops48.decode ni=(QuadraticAlgebra.norm (value x))⁻¹ := by
      change ProverCommitM31Ops48.decode ni=(ProverCommitM31Ops48.decode n)⁻¹ at hvni
      rw [hvni,hnorm]
    apply QuadraticAlgebra.ext
    · change ProverCommitM31Ops48.decode a=_
      rw [hva,hvi,QuadraticAlgebra.re_inv]
      simp only [zero_mul,add_zero]
      change (x.a.val : M31Exact)*(QuadraticAlgebra.norm (value x))⁻¹=(QuadraticAlgebra.norm (value x))⁻¹*(x.a.val : M31Exact)
      ring
    · change ProverCommitM31Ops48.decode b=_
      rw [hvb,hvi]
      change (nb.val : M31Exact)*(QuadraticAlgebra.norm (value x))⁻¹=_
      rw [hvnb,QuadraticAlgebra.im_inv]
      change -(x.b.val : M31Exact)*(QuadraticAlgebra.norm (value x))⁻¹= -((QuadraticAlgebra.norm (value x))⁻¹*(x.b.val : M31Exact))
      ring

#print axioms inverse
end R1Z.ProverRwSuccessComplexInverseExact
