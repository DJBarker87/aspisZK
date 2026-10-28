import R1Z.PV_RunJoin_BasisFactors38
import R1Z.ProverCommitInterpolationInitial48
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_BasisInitial38
open Aeneas Aeneas.Std Result ProverRwFull
variable [ExternalTypes]

theorem source (ops : ExternalFuns) (i : Usize) (hi : i.val<28) :
    @host_sumcheck.interpolation_basis _ (ProverRwP6BodyCandidate.selected ops) i =
      ProverCommitInterpolationInitial48.prepare (UScalar.cast .U8 i) := by
  unfold host_sumcheck.interpolation_basis ProverCommitInterpolationInitial48.prepare
  change (do
    let basis ← Array.update (Array.repeat 28#usize AspisR1ProducerRelease47.field.M31.ZERO)
      0#usize AspisR1ProducerRelease47.field.M31.ONE
    @host_sumcheck.interpolation_basis_steps _ (ProverRwP6BodyCandidate.selected ops)
      basis AspisR1ProducerRelease47.field.M31.ONE 0#usize i 0#usize) = _
  apply congrArg (Aeneas.Std.bind
    (Array.update (Array.repeat 28#usize AspisR1ProducerRelease47.field.M31.ZERO)
      0#usize AspisR1ProducerRelease47.field.M31.ONE))
  funext basis
  have cz : UScalar.cast .U8 (0#usize)=0#u8 := by scalar_tac
  simpa only [cz] using PV_RunJoin_BasisFactors38.source ops 28 i 0#usize 0#usize 28#u8 hi rfl rfl
    (by simp [ProverCommitInterpolationSchedule48.degree]) basis AspisR1ProducerRelease47.field.M31.ONE

/-- All 27 factors of the actual emitted basis helper yield a canonical,
nonzero denominator. No concrete denominator or large array is reduced. -/
theorem complete (ops : ExternalFuns) (i : Usize) (hi : i.val<28) :
    ∃ (ys : Nat → U32) (den : U32),
      @host_sumcheck.interpolation_basis _ (ProverRwP6BodyCandidate.selected ops) i =
        .ok (ProverCommitM31Array48.array 28#usize ys,den) ∧
      (∀ k, k<28 → ProverCommitM31Ops48.canonical (ys k)) ∧
      ProverCommitM31Ops48.canonical den ∧
      ProverCommitBasisPolynomial48.poly ys =
        ProverCommitInterpolationSchedule48.polyProd i.val 0 28 ∧
      ProverCommitM31Ops48.decode den =
        ProverCommitInterpolationSchedule48.denProd i.val 0 28 ∧ den≠0#u32 := by
  rw [source ops i hi]
  have hc : (UScalar.cast .U8 i).val=i.val := by scalar_tac
  simpa only [hc] using ProverCommitInterpolationInitial48.prepare_exact
    (UScalar.cast .U8 i) (by rw [hc];exact hi)

#print axioms source
#print axioms complete
end R1Z.PV_RunJoin_BasisInitial38
