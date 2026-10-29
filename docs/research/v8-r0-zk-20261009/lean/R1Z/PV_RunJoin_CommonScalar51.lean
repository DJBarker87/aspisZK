import R1Z.PV_RunJoin_CommonBlock51
import R1Z.PV_RunJoin_ScalarResultModel50
import R1Z.PV_RunJoin_OriginalOpeningFrames51
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_CommonScalar51
open Aeneas Aeneas.Std Result ProverRwFull PV_RunJoin_WeightInstalled46 R0P R0Z R0Z.JointView R0Z.FsStatement R0Z.HvzkV
open R1Z.GamesR1 R1Z.GamesR1PBin R1Z.CouplingR1PBin R1Z.TranscriptR1 R1Z.EventsR1PBin
open PV_RunJoin_OpeningSampler50 (block)
open PV_RunJoin_CommonRecord51 (record)
open PV_RunJoin_CommonOracle51 (hash)
open PV_RunJoin_OriginalOpeningFrames51 (row)
variable {K CH Aux : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K] {F : Subfield K}
variable (W : R1Wire K CH Aux) (Pr : R1ProverP K CH Aux F W) (R : RomModel W)
  (N : Nat) (hN : 0<N) (h : R0Z.ZkStatement.HonestProver K) (B : PackBasis F)
  (outputs : Statement K CH → Challenges K → Aux) (x : Statement K CH) (w : h.Instance)
  (hin : RAddrIn W Pr R h B outputs x w) (hc : RCausal W Pr h B outputs x w)
  (s : Fin N → AttS (F:=F) W Pr)
  (hcoll : ∀ g g' : Fin (N*n1 W Pr),g'<g →
    addrQ W Pr R N hN h B outputs x w s (AgreeR1PBin.posE W Pr N g')≠
    addrQ W Pr R N hN h B outputs x w s (AgreeR1PBin.posE W Pr N g))
  (hpub : ∀ g,addrQ W Pr R N hN h B outputs x w s (AgreeR1PBin.posE W Pr N g)≠W.pubBytes x)
open ProverCommitWideOps48
open PV_RunJoin_WeightMap46 (mapResult)
set_option allowUnsafeReducibility true in
attribute [local irreducible] ProverRwP6BoundaryInstall.selected
attribute [local irreducible] selected PV_B2_F_RawNative.selected PV_B2_F_ResourceFamilies.selected
include hin hc hcoll hpub

theorem complete (base : ExternalTypes) (heap : Heap) (box : Box) (ops : @ExternalFuns (types base))
    (k : Fin N) (i : Fin 4)
    (payload : Slice U8) (small : payload.length≤U32.max)
    (hp : payload.val.map ProverCommitOwnerBytes42.byte=(record W Pr h B outputs x w (s k).2.1).rest.payload i) :
    let a := PV_RunJoin_SamplerValue49.value base heap box ops (block ((s k).2.1 (.inl (.sqO i))))
      (PV_RunJoin_SamplerValueModel50.nonzero i)
    mapResult (fun pair => (value (PV_RunJoin_ScalarRaw50.raw pair.1),pair.2))
      (@host_transcript.Transcript.scalar (types base) (selected base heap box ops) _
        (@aspis_core.digest.LegacyHashFn.Insts.Aspis_coreDigestDigest32 (types base) (selected base heap box ops))
        ⟨block (fieldVal (fc (.absO i)) (record W Pr h B outputs x w (s k).2.1)),hash W (toRP W Pr R h B outputs x w hN s).1⟩
        (row i) payload (PV_RunJoin_SamplerValueModel50.nonzero i))=(do
      let _ ← @trace.value (types base) (selected base heap box ops) 4#u16
        (UScalar.cast .Usize (row i)) (ProverRwDictionaryTower.fromW (source a))
      ok (PhaseSamplerParserBin.openingScalar i ((s k).2.1 (.inl (.sqO i))),
        ({state:=block ((s k).2.1 (.inl (.advO i))),hash:=hash W (toRP W Pr R h B outputs x w hN s).1} : host_transcript.Transcript _))) := by
  dsimp only
  rw [PV_RunJoin_ScalarResultModel50.complete]
  unfold PV_RunJoin_ScalarResultModel50.retained
  rw [PV_RunJoin_CommonBlock51.complete W Pr R N hN h B outputs x w hin hc s hcoll hpub base heap box ops k i payload small hp]
  simp only [bind_tc_ok]
  dsimp only [Aeneas.Std.uncurry]
  simp only [bind_tc_ok,lift,PV_RunJoin_OpeningBlockEquiv50.inverse]
#print axioms complete
end R1Z.PV_RunJoin_CommonScalar51
