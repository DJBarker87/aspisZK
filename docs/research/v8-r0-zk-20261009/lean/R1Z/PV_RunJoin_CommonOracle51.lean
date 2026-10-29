import R1Z.AgreeR1PBin
import R1Z.PV_RunJoin_OpeningByteCodec51
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_CommonOracle51
open Aeneas Aeneas.Std R0P R0Z R0Z.JointView R0Z.FsStatement R0Z.HvzkV
open R1Z.GamesR1 R1Z.GamesR1PBin R1Z.CouplingR1PBin R1Z.TranscriptR1 R1Z.EventsR1PBin
variable {K CH Aux : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K] {F : Subfield K}

def hash (W : R1Wire K CH Aux) (tab : W.Tab) : ProverRwFull.aspis_core.digest.LegacyHashFn :=
  fun parts => .ok (PV_RunJoin_OpeningSampler50.block (W.look tab (ProverRwOuterFrames.flatten parts)))

variable (W : R1Wire K CH Aux) (Pr : R1ProverP K CH Aux F W) (R : RomModel W)
  (N : Nat) (hN : 0<N) (h : R0Z.ZkStatement.HonestProver K) (B : PackBasis F)
  (outputs : Statement K CH → Challenges K → Aux) (x : Statement K CH) (w : h.Instance)

theorem read (hin : RAddrIn W Pr R h B outputs x w) (hc : RCausal W Pr h B outputs x w)
    (s : Fin N → AttS (F:=F) W Pr)
    (hcoll : ∀ g g' : Fin (N*n1 W Pr),g'<g →
      addrQ W Pr R N hN h B outputs x w s (AgreeR1PBin.posE W Pr N g')≠
      addrQ W Pr R N hN h B outputs x w s (AgreeR1PBin.posE W Pr N g))
    (hpub : ∀ g,addrQ W Pr R N hN h B outputs x w s (AgreeR1PBin.posE W Pr N g)≠W.pubBytes x)
    (k : Fin N) (j : TRead) (parts : Slice (Slice U8))
    (address : ProverRwOuterFrames.flatten parts=addrQ W Pr R N hN h B outputs x w s (k,.inl j)) :
    hash W (toRP W Pr R h B outputs x w hN s).1 parts=
      .ok (PV_RunJoin_OpeningSampler50.block ((s k).2.1 (.inl j))) := by
  have run := AgreeR1PBin.run_eq_lazy W Pr R N hN h B outputs x w hin hc s hcoll hpub
  unfold hash
  rw [address,AgreeR1PBin.look_toRP]
  rw [AgreeR1PBin.ans_eq W Pr R N hN h B outputs x w hin hc s run k (.inl j)]
#print axioms hash
#print axioms read
end R1Z.PV_RunJoin_CommonOracle51
