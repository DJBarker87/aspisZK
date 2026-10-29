import R1Z.PV_RunJoin_OriginalBlock51
import R1Z.PV_RunJoin_ScalarResultModel50
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_OriginalScalar51
open Aeneas Aeneas.Std Result ProverRwFull
open R0Z R0Z.JointView R0Z.FsStatement R1Z.GamesR1 R1Z.TranscriptR1 R1Z.Batched
open PV_RunJoin_WeightInstalled46 ProverCommitWideOps48
open PV_RunJoin_OpeningSampler50 (block)
open PV_RunJoin_OriginalHash51 (hash)
open PV_RunJoin_OriginalOpeningFrames51 (row)
open PV_RunJoin_WeightMap46 (mapResult)
variable {K CH Aux : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K]
set_option allowUnsafeReducibility true in
attribute [local irreducible] ProverRwP6BoundaryInstall.selected
attribute [local irreducible] selected PV_B2_F_RawNative.selected PV_B2_F_ResourceFamilies.selected

theorem complete (base : ExternalTypes) (heap : Heap) (box : Box) (ops : @ExternalFuns (types base))
    (W : R1Wire K CH Aux) (x : Statement K CH) (V : View K CH Aux R1Bat)
    (c : R1Coins W.Cm W.Tab) (tab : W.Tab)
    (unique : ((verLog W x V c).map Prod.fst).Nodup) (i : Fin 4)
    (payload : Slice U8) (small : payload.length≤U32.max)
    (hp : payload.val.map ProverCommitOwnerBytes42.byte=(recP W x V c.1 c.2.1).rest.payload i) :
    let a := PV_RunJoin_SamplerValue49.value base heap box ops (block (c.1 (.sqO i)))
      (PV_RunJoin_SamplerValueModel50.nonzero i)
    mapResult (fun pair => (value (PV_RunJoin_ScalarRaw50.raw pair.1),pair.2))
      (@host_transcript.Transcript.scalar (types base) (selected base heap box ops) _
        (@aspis_core.digest.LegacyHashFn.Insts.Aspis_coreDigestDigest32 (types base) (selected base heap box ops))
        ⟨block (fieldVal (fc (.absO i)) (recP W x V c.1 c.2.1)),hash W x V c tab⟩
        (row i) payload (PV_RunJoin_SamplerValueModel50.nonzero i))=(do
      let _ ← @trace.value (types base) (selected base heap box ops) 4#u16
        (UScalar.cast .Usize (row i)) (ProverRwDictionaryTower.fromW (source a))
      ok (PhaseSamplerParserBin.openingScalar i (c.1 (.sqO i)),
        ({state:=block (c.1 (.advO i)),hash:=hash W x V c tab} : host_transcript.Transcript _))) := by
  dsimp only
  rw [PV_RunJoin_ScalarResultModel50.complete]
  unfold PV_RunJoin_ScalarResultModel50.retained
  rw [PV_RunJoin_OriginalBlock51.complete base heap box ops W x V c tab unique i payload small hp]
  simp only [bind_tc_ok,lift,PV_RunJoin_OpeningBlockEquiv50.inverse]
#print axioms complete
end R1Z.PV_RunJoin_OriginalScalar51
