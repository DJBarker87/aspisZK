import R1Z.PV_RunJoin_OpeningSampler50
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_OpeningBlock50
open Aeneas Aeneas.Std Result ProverRwFull
open PV_RunJoin_WeightInstalled46 ProverCommitWideOps48
open R0Z.FsStatement

def answer (b : Array U8 32#usize) : OracleAnswer :=
  R1J.SamplerLawSpend.stateEquiv.symm (AspisV8R19.SqueezeOracleBridge.decodeState b)

theorem state (b : Array U8 32#usize) :
    PhaseSamplerParserBin.state (answer b)=AspisV8R19.SqueezeOracleBridge.decodeState b :=
  R1J.SamplerLawSpend.stateEquiv.apply_symm_apply _

theorem roundtrip (b : Array U8 32#usize) : PV_RunJoin_OpeningSampler50.block (answer b)=b := by
  unfold PV_RunJoin_OpeningSampler50.block
  rw [state,AspisV8R19.SqueezeOracleBridge.array_roundtrip]

theorem complete (base : ExternalTypes) (heap : Heap) (box : Box) (ops : @ExternalFuns (types base))
    (i : Fin 4) (b : Array U8 32#usize) :
    ∃ a : Raw,(if i=0 then @sampler.gamma_sample (types base) (selected base heap box ops) b
      else @sampler.ordinary_sample (types base) (selected base heap box ops) b)=
      ok (ProverRwDictionaryTower.fromW (source a)) ∧ canonical a ∧
      value a=PhaseSamplerParserBin.openingScalar i (answer b) := by
  have result := PV_RunJoin_OpeningSampler50.complete base heap box ops i (answer b)
  rw [roundtrip] at result
  exact result
#print axioms answer
#print axioms state
#print axioms roundtrip
#print axioms complete
end R1Z.PV_RunJoin_OpeningBlock50
