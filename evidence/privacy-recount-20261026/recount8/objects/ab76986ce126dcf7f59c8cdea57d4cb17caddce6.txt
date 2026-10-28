import R1Z.PV_RunJoin_SourceArray44
import R1Z.ProverRwP6PowersGammaSource
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_GammaPowers44
open Aeneas Aeneas.Std Result ProverRwFull
open ProverCommitWideOps48 ProverCommitMix48 PV_RunJoin_WideArithmetic44
variable [ExternalTypes]

/-- Source-only powers installation. Native callback association remains a
separate obligation; no runtime or deployment credit follows from this definition. -/
@[reducible] def inputs (ops : ExternalFuns) : ExternalFuns := { ops with op254 := ProverRwP6PowersInstall.powers ops }
abbrev dict (ops : ExternalFuns) := ProverRwP6BodyCandidate.selected (inputs ops)

theorem gamma (ops : ExternalFuns) (g : Raw) (hg : canonical g) :
    ∃ p : Nat → Raw, (dict ops).op254 29#usize (current (source g)) =
      .ok (PV_RunJoin_BatchRowValue44.array 29#usize p) ∧
      (∀ i, i < 29 → canonical (p i)) ∧
      ∀ i, i < 29 → value (p i) = value g ^ i := by
  obtain ⟨p,hp,hcp,hdp⟩ := ProverCommitGamma48.gamma_exact g hg
  refine ⟨p,?_,hcp,hdp⟩
  change ProverRwP6PowersInstall.powers ops 29#usize (current (source g)) = _
  have bridge := ProverRwP6PowersGammaSource.gamma ops (current (source g))
  change ProverRwP6PowersInstall.powers ops 29#usize (current (source g)) = _ at bridge
  rw [bridge]
  change ProverRwP6ResultMap.map (ProverRwP6ArrayMap.map current)
    (AspisR1ProducerRelease47.gamma (ProverRwDictionaryTower.toW (ProverRwDictionaryTower.fromW (source g)))) = _
  rw [ProverRwDictionaryTower.native_w_roundtrip,hp]
  change Result.ok (ProverRwP6ArrayMap.map current (sourceArray 29#usize p)) = _
  rw [PV_RunJoin_SourceArray44.map]
#print axioms gamma
end R1Z.PV_RunJoin_GammaPowers44
