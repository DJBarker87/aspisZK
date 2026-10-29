import R1Z.PV_RunJoin_OriginalHash51
import R1Z.PV_RunJoin_OriginalOpeningFrames51
import R1Z.PV_RunJoin_TranscriptDigest51
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_OriginalBlock51
open Aeneas Aeneas.Std Result ProverRwFull
open R0Z R0Z.JointView R0Z.FsStatement R1Z.GamesR1 R1Z.TranscriptR1 R1Z.Batched
open PV_RunJoin_WeightInstalled46
open PV_RunJoin_OpeningSampler50 (block)
open PV_RunJoin_OriginalHash51 (hash)
open PV_RunJoin_OriginalOpeningFrames51 (row)
variable {K CH Aux : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K]

theorem complete (base : ExternalTypes) (heap : Heap) (box : Box) (ops : @ExternalFuns (types base))
    (W : R1Wire K CH Aux) (x : Statement K CH) (V : View K CH Aux R1Bat)
    (c : R1Coins W.Cm W.Tab) (tab : W.Tab)
    (unique : ((verLog W x V c).map Prod.fst).Nodup) (i : Fin 4)
    (payload : Slice U8) (small : payload.length≤U32.max)
    (hp : payload.val.map ProverCommitOwnerBytes42.byte=(recP W x V c.1 c.2.1).rest.payload i) :
    @host_transcript.Transcript.block _
      (@aspis_core.digest.LegacyHashFn.Insts.Aspis_coreDigestDigest32 (types base) (selected base heap box ops))
      ⟨block (fieldVal (fc (.absO i)) (recP W x V c.1 c.2.1)),hash W x V c tab⟩ (row i) payload=
        ok (block (c.1 (.sqO i)),⟨block (c.1 (.advO i)),hash W x V c tab⟩) := by
  rw [PV_RunJoin_TranscriptDigest51.block]
  have ha := PV_RunJoin_OriginalHash51.read W x V c tab unique (.absO i) _
    (PV_RunJoin_OriginalOpeningFrames51.absorb _ i payload small hp)
  change (do
    let absorbed ← hash W x V c tab (PV_RunJoin_TranscriptAbsorb51.request
      (block (fieldVal (fc (.absO i)) (recP W x V c.1 c.2.1))) (row i) payload)
    let b ← hash W x V c tab (PV_RunJoin_TranscriptRequests51.message absorbed 1#u8)
    let advanced ← hash W x V c tab (PV_RunJoin_TranscriptRequests51.message absorbed 2#u8)
    ok (b,({state:=advanced,hash:=hash W x V c tab} : host_transcript.Transcript _)))=_
  rw [ha]
  simp only [bind_tc_ok]
  rw [PV_RunJoin_OriginalHash51.read W x V c tab unique (.sqO i) _
    (PV_RunJoin_OriginalOpeningFrames51.squeeze _ i)]
  simp only [bind_tc_ok]
  rw [PV_RunJoin_OriginalHash51.read W x V c tab unique (.advO i) _
    (PV_RunJoin_OriginalOpeningFrames51.advance _ i)]
  rfl
#print axioms complete
end R1Z.PV_RunJoin_OriginalBlock51
