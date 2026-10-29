import R1Z.PV_RunJoin_SamplerValueModel50
import R1Z.PV_RunJoin_ScalarSource49
import R1Z.PV_RunJoin_ResultMap50
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_ScalarResultModel50
open Aeneas Aeneas.Std Result ProverRwFull
open PV_RunJoin_WeightInstalled46 ProverCommitWideOps48
open PV_RunJoin_WeightMap46 (mapResult)

def retained (base : ExternalTypes) (heap : Heap) (box : Box) (ops : @ExternalFuns (types base))
    {H : Type} (D : aspis_core.digest.Digest32 H) (self : host_transcript.Transcript H)
    (i : Fin 4) (row : U8) (payload : Slice U8) : Result (Exact × host_transcript.Transcript H) := do
  let (block,next) ← @host_transcript.Transcript.block H D self row payload
  let a := PV_RunJoin_SamplerValue49.value base heap box ops block (PV_RunJoin_SamplerValueModel50.nonzero i)
  let index ← Aeneas.Std.lift (UScalar.cast .Usize row)
  let _ ← @trace.value (types base) (selected base heap box ops) 4#u16 index (ProverRwDictionaryTower.fromW (source a))
  ok (PhaseSamplerParserBin.openingScalar i (PV_RunJoin_OpeningBlock50.answer block),next)
set_option allowUnsafeReducibility true in
attribute [local irreducible] ProverRwP6BoundaryInstall.selected
attribute [local irreducible] selected PV_B2_F_RawNative.selected PV_B2_F_ResourceFamilies.selected

theorem complete (base : ExternalTypes) (heap : Heap) (box : Box) (ops : @ExternalFuns (types base))
    {H : Type} (D : aspis_core.digest.Digest32 H) (self : host_transcript.Transcript H)
    (i : Fin 4) (row : U8) (payload : Slice U8) :
    mapResult (fun pair => (value (PV_RunJoin_ScalarRaw50.raw pair.1),pair.2))
      (@host_transcript.Transcript.scalar (types base) (selected base heap box ops) H D self row payload
        (PV_RunJoin_SamplerValueModel50.nonzero i))=retained base heap box ops D self i row payload := by
  rw [PV_RunJoin_ScalarSource49.complete]
  unfold PV_RunJoin_ScalarSource49.retained retained
  rw [PV_RunJoin_ResultMap50.bind]
  apply congrArg (Aeneas.Std.bind _)
  funext pair
  rcases pair with ⟨block,next⟩
  dsimp only [Aeneas.Std.uncurry]
  simp only [lift,bind_tc_ok]
  rw [PV_RunJoin_ResultMap50.bind]
  apply congrArg (Aeneas.Std.bind _)
  funext unit
  simp only [mapResult,PV_RunJoin_ScalarRaw50.roundtrip,PV_RunJoin_SamplerValueModel50.complete]
#print axioms retained
#print axioms complete
end R1Z.PV_RunJoin_ScalarResultModel50
