import R1Z.PV_RunJoin_SamplerValueModel50
import R1Z.PV_RunJoin_ScalarSuccess49
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_ScalarSuccessModel50
open Aeneas Aeneas.Std Result ProverRwFull
open PV_RunJoin_WeightInstalled46 ProverCommitWideOps48

theorem complete (base : ExternalTypes) (heap : Heap) (box : Box) (ops : @ExternalFuns (types base))
    {H : Type} (D : aspis_core.digest.Digest32 H) (self : host_transcript.Transcript H)
    (i : Fin 4) (row : U8) (payload : Slice U8)
    (out : aspis_core.field.wide_exact.WideExact) (next : host_transcript.Transcript H)
    (h : @host_transcript.Transcript.scalar (types base) (selected base heap box ops) H D self row payload
      (PV_RunJoin_SamplerValueModel50.nonzero i)=ok (out,next)) :
    ∃ (block : Array U8 32#usize) (a : Raw),
      @host_transcript.Transcript.block H D self row payload=ok (block,next) ∧
      canonical a ∧ out=ProverRwDictionaryTower.fromW (source a) ∧
      value a=PhaseSamplerParserBin.openingScalar i (PV_RunJoin_OpeningBlock50.answer block) := by
  obtain ⟨block,a,hblock,hca,ha,hav⟩ := PV_RunJoin_ScalarSuccess49.complete base heap box ops D
    self row payload (PV_RunJoin_SamplerValueModel50.nonzero i) out next h
  refine ⟨block,a,hblock,hca,ha,?_⟩
  rw [hav]
  exact PV_RunJoin_SamplerValueModel50.complete base heap box ops i block
#print axioms complete
end R1Z.PV_RunJoin_ScalarSuccessModel50
