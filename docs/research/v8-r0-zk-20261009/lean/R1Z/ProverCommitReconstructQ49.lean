import R1Z.ProverCommitReconstructC49
import R1Z.ProverCommitNativeQ48
/-! Complete current nine-channel QM31 reconstruction. Input totals are
arbitrary U64 words; accumulation/component provenance is a separate caller. -/
set_option autoImplicit false
namespace R1Z.ProverCommitReconstructQ49
open Aeneas Aeneas.Std Result AspisR1ProducerRelease47
open ProverCommitPrimitive47 ProverCommitSubfieldOps47
open AspisV8R15.ExactTowerBase
open AspisR1.ExtractedCurrentQM31Exact (decode)

def matrix (s : Nat → Nat → U64) : Array (Array U64 3#usize) 3#usize :=
  ProverCommitArray49.array 3#usize (fun i => ProverCommitArray49.array 3#usize (s i))

theorem index (s : Nat → Nat → U64) (i : Usize) (hi : i.val<3) :
    Array.index_usize (matrix s) i=ok (ProverCommitArray49.array 3#usize (s i.val)) := by
  rw [matrix,ProverCommitArray49.index _ _ _ hi]

def model (s : Nat → Nat → U64) : QM31Exact :=
  ⟨ProverCommitReconstructC49.model (s 0)+qm31R*ProverCommitReconstructC49.model (s 1),
    ProverCommitReconstructC49.model (s 2)-ProverCommitReconstructC49.model (s 0)-ProverCommitReconstructC49.model (s 1)⟩

theorem exact_result (s : Nat → Nat → U64) :
    ∃ z : Old.Q, reconstruction.q (matrix s)=ok (ProverCommitNativeQ48.source z) ∧
      Canonical z ∧ decode z=model s := by
  obtain ⟨m0,hm0,hc0,hv0⟩ := ProverCommitReconstructC49.exact_result (s 0)
  obtain ⟨m1,hm1,hc1,hv1⟩ := ProverCommitReconstructC49.exact_result (s 1)
  obtain ⟨m2,hm2,hc2,hv2⟩ := ProverCommitReconstructC49.exact_result (s 2)
  obtain ⟨r,hr,hcr,hvr⟩ := ProverCommitNativeC49.mul_r m1 hc1
  have hr' : reconstruction.mul_r (ProverCommitNativeC49.source m1)=ok (ProverCommitNativeC49.source r) := hr
  obtain ⟨lo,hlo,hclo,hvlo⟩ := ProverCommitNativeC49.add m0 r hc0 hcr
  obtain ⟨t,ht,hct,hvt⟩ := ProverCommitNativeC49.sub m2 m0 hc2 hc0
  obtain ⟨hi,hhi,hchi,hvhi⟩ := ProverCommitNativeC49.sub t m1 hct hc1
  refine ⟨⟨lo,hi⟩,?_,⟨hclo,hchi⟩,?_⟩
  · simp only [reconstruction.q,index s 0#usize (by decide),index s 1#usize (by decide),
      index s 2#usize (by decide),show (0#usize).val=0 from rfl,show (1#usize).val=1 from rfl,
      show (2#usize).val=2 from rfl,hm0,hm1,hm2,hr',hlo,ht,hhi,bind_tc_ok]
    rfl
  · apply QuadraticAlgebra.ext
    · change ProverCommitNativeC49.value lo=ProverCommitReconstructC49.model (s 0)+qm31R*ProverCommitReconstructC49.model (s 1)
      rw [hvlo,hv0,hvr,hv1]
    · change ProverCommitNativeC49.value hi=ProverCommitReconstructC49.model (s 2)-ProverCommitReconstructC49.model (s 0)-ProverCommitReconstructC49.model (s 1)
      rw [hvhi,hvt,hv2,hv0,hv1]

#print axioms index
#print axioms exact_result
end R1Z.ProverCommitReconstructQ49
