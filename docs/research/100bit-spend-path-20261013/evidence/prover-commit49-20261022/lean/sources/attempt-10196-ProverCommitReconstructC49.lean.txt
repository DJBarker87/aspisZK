import AspisR1ProducerRelease47.Reconstruction49
import R1Z.ProverCommitNativeSquare49
import R1Z.ProverCommitArray49
/-! Current native three-channel CM31 reconstruction, for arbitrary U64 sums. -/
set_option autoImplicit false
namespace R1Z.ProverCommitReconstructC49
open Aeneas Aeneas.Std Result AspisR1ProducerRelease47
open ProverCommitPrimitive47 ProverCommitNativeC49
open AspisV8R15.ExactTowerBase

def model (s : Nat → U64) : CM31Exact :=
  ⟨(s 0).val-(s 1).val,(s 2).val-(s 0).val-(s 1).val⟩

theorem exact_result (s : Nat → U64) :
    ∃ z : Old.C, reconstruction.cm (ProverCommitArray49.array 3#usize s)=ok (source z) ∧
      Canonical z ∧ value z=model s := by
  obtain ⟨m0,hm0,hc0,hv0⟩ := ProverCommitNativeSquare49.reduce_exact (s 0)
  obtain ⟨m1,hm1,hc1,hv1⟩ := ProverCommitNativeSquare49.reduce_exact (s 1)
  obtain ⟨m2,hm2,hc2,hv2⟩ := ProverCommitNativeSquare49.reduce_exact (s 2)
  obtain ⟨a,ha,hca,hva⟩ := ProverCommitM31Ops48.sub_exact m0 m1 hc0 hc1
  obtain ⟨b0,hb0,hcb0,hvb0⟩ := ProverCommitM31Ops48.sub_exact m2 m0 hc2 hc0
  obtain ⟨b,hb,hcb,hvb⟩ := ProverCommitM31Ops48.sub_exact b0 m1 hcb0 hc1
  refine ⟨⟨a,b⟩,?_,⟨hca,hcb⟩,?_⟩
  · simp only [reconstruction.cm,
      ProverCommitArray49.index 3#usize s 0#usize (by decide),
      ProverCommitArray49.index 3#usize s 1#usize (by decide),
      ProverCommitArray49.index 3#usize s 2#usize (by decide),
      show (0#usize).val=0 from rfl,show (1#usize).val=1 from rfl,show (2#usize).val=2 from rfl,
      hm0,hm1,hm2,ha,hb0,hb,bind_tc_ok,source,ProverCommitRelease47.convC,fromC]
  · change (a.val : M31Exact)=(m0.val : M31Exact)-(m1.val : M31Exact) at hva
    change (b0.val : M31Exact)=(m2.val : M31Exact)-(m0.val : M31Exact) at hvb0
    change (b.val : M31Exact)=(b0.val : M31Exact)-(m1.val : M31Exact) at hvb
    apply QuadraticAlgebra.ext
    · change (a.val : M31Exact)=_
      rw [hva,hv0,hv1]
      rfl
    · change (b.val : M31Exact)=_
      rw [hvb,hvb0,hv2,hv0,hv1]
      rfl

#print axioms exact_result
end R1Z.ProverCommitReconstructC49
