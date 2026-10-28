import R1Z.ProverCommitWideScalar48
import R1Z.PV_RunJoin_FoldCell44
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_DualCell44
open Aeneas Aeneas.Std Result AspisR1ProducerRelease47
open ProverCommitWideOps48 ProverCommitMix48
variable [ProverRwFull.ExternalTypes]
open PV_RunJoin_WideArithmetic44 PV_RunJoin_FoldCell44 (array)
attribute [local irreducible] sourceArray source value

def polynomial (q : Nat → Raw) (a : Exact) : Exact :=
  (value (q 0)+a*value (q 3)+a^2*value (q 2)+a^3*value (q 1))*
    ProverCommitWideScalar48.factor 536870912#u32

theorem cell (ops : ProverRwFull.ExternalFuns) (q : Nat → Raw) (hq : ∀ j, j<4 → canonical (q j))
    (a : Raw) (ha : canonical a) :
    ∃ z : Raw, @ProverRwFull.prover.fold_cell _ (ProverRwP6BodyCandidate.selected ops)
      (array 4#usize q) (current (source a)) true=ok (current (source z)) ∧
      canonical z ∧ value z=polynomial q (value a) := by
  obtain ⟨m1,hm1,hcm1,hdm1⟩ := mul_exact a (q 1) ha (hq 1 (by decide))
  obtain ⟨s2,hs2,hcs2,hds2⟩ := add_exact (q 2) m1 (hq 2 (by decide)) hcm1
  obtain ⟨m2,hm2,hcm2,hdm2⟩ := mul_exact a s2 ha hcs2
  obtain ⟨s3,hs3,hcs3,hds3⟩ := add_exact (q 3) m2 (hq 3 (by decide)) hcm2
  obtain ⟨m3,hm3,hcm3,hdm3⟩ := mul_exact a s3 ha hcs3
  obtain ⟨h,hh,hch,hdh⟩ := add_exact (q 0) m3 (hq 0 (by decide)) hcm3
  obtain ⟨hz,hcz,hdz⟩ := ProverCommitWideScalar48.source_exact h 536870912#u32
  refine ⟨ProverCommitWideScalar48.product h 536870912#u32,?_,hcz,?_⟩
  · rw [ProverRwFull.prover.fold_cell]
    simp only [↓reduceIte]
    rw [ProverCommitArray49.index _ _ 0#usize (by decide),
      ProverCommitArray49.index _ _ 3#usize (by decide),
      ProverCommitArray49.index _ _ 2#usize (by decide),
      ProverCommitArray49.index _ _ 1#usize (by decide)]
    simp only [show (0#usize).val=0 from rfl,show (1#usize).val=1 from rfl,
      show (2#usize).val=2 from rfl,show (3#usize).val=3 from rfl,
      bind_tc_ok,ProverRwFull.weights.QUARTER,
      PV_RunJoin_WideArithmetic44.mul ops _ _ _ hm1,
      PV_RunJoin_WideArithmetic44.add ops _ _ _ hs2,
      PV_RunJoin_WideArithmetic44.mul ops _ _ _ hm2,
      PV_RunJoin_WideArithmetic44.add ops _ _ _ hs3,
      PV_RunJoin_WideArithmetic44.mul ops _ _ _ hm3,
      PV_RunJoin_WideArithmetic44.add ops _ _ _ hh,
      PV_RunJoin_WideArithmetic44.scale ops _ _ _ hz]
  · rw [hdz,hdh,hdm3,hds3,hdm2,hds2,hdm1,polynomial]
    ring

#print axioms cell
end R1Z.PV_RunJoin_DualCell44
