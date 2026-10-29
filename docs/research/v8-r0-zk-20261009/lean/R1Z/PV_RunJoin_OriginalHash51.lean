import R1Z.PV_RunJoin_OriginalTable51
import R1Z.PV_RunJoin_OpeningByteCodec51
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_OriginalHash51
open Aeneas Aeneas.Std R0Z R0Z.JointView R0Z.FsStatement R1Z.GamesR1 R1Z.TranscriptR1 R1Z.Batched
variable {K CH Aux : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K]

def hash (W : R1Wire K CH Aux) (x : Statement K CH) (V : View K CH Aux R1Bat)
    (c : R1Coins W.Cm W.Tab) (tab : W.Tab) : ProverRwFull.aspis_core.digest.LegacyHashFn :=
  fun parts => .ok (PV_RunJoin_OpeningSampler50.block
    (progOracle W x V c tab (ProverRwOuterFrames.flatten parts)))

theorem read (W : R1Wire K CH Aux) (x : Statement K CH) (V : View K CH Aux R1Bat)
    (c : R1Coins W.Cm W.Tab) (tab : W.Tab)
    (unique : ((verLog W x V c).map Prod.fst).Nodup) (j : TRead)
    (parts : Slice (Slice U8))
    (address : ProverRwOuterFrames.flatten parts=addr j (recP W x V c.1 c.2.1)) :
    hash W x V c tab parts=.ok (PV_RunJoin_OpeningSampler50.block (c.1 j)) := by
  unfold hash
  rw [address,PV_RunJoin_OriginalTable51.read W x V c tab unique j]
#print axioms hash
#print axioms read
end R1Z.PV_RunJoin_OriginalHash51
