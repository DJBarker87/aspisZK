import R1Z.PV_RunJoin_CommonRecord51
import R1Z.PV_RunJoin_SemanticFrames51
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_CommonSemanticReads51
open Aeneas Aeneas.Std R0P R0Z R0Z.JointView R0Z.FsStatement R0Z.HvzkV
open R1Z.GamesR1 R1Z.GamesR1PBin R1Z.CouplingR1PBin R1Z.TranscriptR1 R1Z.EventsR1PBin
open PV_RunJoin_OpeningSampler50 (block)
open PV_RunJoin_CommonRecord51 (record)
open PV_RunJoin_CommonOracle51 (hash)
open PV_RunJoin_SemanticFrames51 (row)
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
include hin hc hcoll hpub

theorem absorb (k : Fin N) (i : Fin 27) (framed : Slice U8)
    (hp : framed.val.map ProverCommitOwnerBytes42.byte=(record W Pr h B outputs x w (s k).2.1).rest.framed i) :
    hash W (toRP W Pr R h B outputs x w hN s).1
      (PV_RunJoin_SemanticRequests51.request
        (block (fieldVal (fc (.absS i)) (record W Pr h B outputs x w (s k).2.1))) (row i) framed)=
      .ok (block ((s k).2.1 (.inl (.absS i)))) := by
  apply PV_RunJoin_CommonOracle51.read W Pr R N hN h B outputs x w hin hc s hcoll hpub k (.absS i)
  exact (PV_RunJoin_SemanticFrames51.absorb _ i framed hp).trans
    (PV_RunJoin_CommonRecord51.address W Pr h B outputs x w R N hN s k (.absS i))

theorem squeeze (k : Fin N) (i : Fin 27) :
    hash W (toRP W Pr R h B outputs x w hN s).1
      (PV_RunJoin_TranscriptRequests51.message (block ((s k).2.1 (.inl (.absS i)))) 1#u8)=
      .ok (block ((s k).2.1 (.inl (.sqS i)))) := by
  apply PV_RunJoin_CommonOracle51.read W Pr R N hN h B outputs x w hin hc s hcoll hpub k (.sqS i)
  exact (PV_RunJoin_SemanticFrames51.squeeze (record W Pr h B outputs x w (s k).2.1) i).trans
    (PV_RunJoin_CommonRecord51.address W Pr h B outputs x w R N hN s k (.sqS i))

theorem advance (k : Fin N) (i : Fin 27) :
    hash W (toRP W Pr R h B outputs x w hN s).1
      (PV_RunJoin_TranscriptRequests51.message (block ((s k).2.1 (.inl (.absS i)))) 2#u8)=
      .ok (block ((s k).2.1 (.inl (.advS i)))) := by
  apply PV_RunJoin_CommonOracle51.read W Pr R N hN h B outputs x w hin hc s hcoll hpub k (.advS i)
  exact (PV_RunJoin_SemanticFrames51.advance (record W Pr h B outputs x w (s k).2.1) i).trans
    (PV_RunJoin_CommonRecord51.address W Pr h B outputs x w R N hN s k (.advS i))
#print axioms absorb
#print axioms squeeze
#print axioms advance
end R1Z.PV_RunJoin_CommonSemanticReads51
