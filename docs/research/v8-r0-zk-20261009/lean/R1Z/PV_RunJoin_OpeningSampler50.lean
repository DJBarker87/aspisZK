import R1Z.PV_RunJoin_SamplerOrdinaryModel50
import R1Z.PV_RunJoin_SamplerGammaModel50
import R1Z.PhaseSamplerParserBin
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_OpeningSampler50
open Aeneas Aeneas.Std Result ProverRwFull
open PV_RunJoin_WeightInstalled46 ProverCommitWideOps48
open R0Z.FsStatement

def block (b : OracleAnswer) : Array U8 32#usize :=
  AspisV8R19.SqueezeOracleBridge.encodeState (PhaseSamplerParserBin.state b)

theorem state (b : OracleAnswer) :
    AspisV8R19.SqueezeOracleBridge.decodeState (block b)=PhaseSamplerParserBin.state b :=
  AspisV8R19.SqueezeOracleBridge.state_roundtrip _
set_option allowUnsafeReducibility true in
attribute [local irreducible] ProverRwP6BoundaryInstall.selected
attribute [local irreducible] selected PV_B2_F_RawNative.selected PV_B2_F_ResourceFamilies.selected

theorem complete (base : ExternalTypes) (heap : Heap) (box : Box) (ops : @ExternalFuns (types base))
    (i : Fin 4) (b : OracleAnswer) :
    ∃ a : Raw,(if i=0 then @sampler.gamma_sample (types base) (selected base heap box ops) (block b)
      else @sampler.ordinary_sample (types base) (selected base heap box ops) (block b))=
      ok (ProverRwDictionaryTower.fromW (source a)) ∧ canonical a ∧
      value a=PhaseSamplerParserBin.openingScalar i b := by
  by_cases hi : i=0
  · obtain ⟨a,ha,hc,hm⟩ := PV_RunJoin_SamplerGammaModel50.complete base heap box ops (block b)
    refine ⟨a,by rw [if_pos hi];exact ha,hc,?_⟩
    rw [state] at hm
    simpa only [PhaseSamplerParserBin.openingScalar,if_pos hi,R0C.ModuloField.gamma] using hm
  · obtain ⟨a,ha,hc,hm⟩ := PV_RunJoin_SamplerOrdinaryModel50.complete base heap box ops (block b)
    refine ⟨a,by rw [if_neg hi];exact ha,hc,?_⟩
    rw [state] at hm
    simpa only [PhaseSamplerParserBin.openingScalar,if_neg hi] using hm
#print axioms block
#print axioms state
#print axioms complete
end R1Z.PV_RunJoin_OpeningSampler50
