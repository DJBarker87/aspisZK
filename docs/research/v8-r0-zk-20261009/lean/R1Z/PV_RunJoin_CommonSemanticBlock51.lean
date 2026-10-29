import R1Z.PV_RunJoin_CommonSemanticReads51
import R1Z.PV_RunJoin_SemanticDigest51
import R1Z.PV_RunJoin_SemanticFrames51
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_CommonSemanticBlock51
open Aeneas Aeneas.Std Result ProverRwFull PV_RunJoin_WeightInstalled46 R0P R0Z R0Z.JointView R0Z.FsStatement R0Z.HvzkV
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

theorem complete (base : ExternalTypes) (heap : Heap) (box : Box) (ops : @ExternalFuns (types base))
    (k : Fin N) (i : Fin 27) (framed : Slice U8)
    (hp : framed.val.map ProverCommitOwnerBytes42.byte=(record W Pr h B outputs x w (s k).2.1).rest.framed i) :
    @host_wire.SemanticTranscript.sample_block_validated _
      (@aspis_core.digest.LegacyHashFn.Insts.Aspis_coreDigestDigest32 (types base) (selected base heap box ops))
      ⟨block (fieldVal (fc (.absS i)) (record W Pr h B outputs x w (s k).2.1)),
        hash W (toRP W Pr R h B outputs x w hN s).1,row i⟩ (row i) framed=
      ok (core.result.Result.Ok (block ((s k).2.1 (.inl (.sqS i)))),
        ⟨block ((s k).2.1 (.inl (.advS i))),hash W (toRP W Pr R h B outputs x w hN s).1,U8.wrapping_add (row i) 1#u8⟩) := by
  rw [PV_RunJoin_SemanticDigest51.source]
  simp only [bne_self_eq_false,Bool.false_eq_true,if_false]
  have ha := PV_RunJoin_CommonSemanticReads51.absorb W Pr R N hN h B outputs x w hin hc s hcoll hpub k i framed hp
  change (do
    let absorbed ← hash W (toRP W Pr R h B outputs x w hN s).1
      (PV_RunJoin_SemanticRequests51.request
        (block (fieldVal (fc (.absS i)) (record W Pr h B outputs x w (s k).2.1))) (row i) framed)
    let b ← hash W (toRP W Pr R h B outputs x w hN s).1 (PV_RunJoin_TranscriptRequests51.message absorbed 1#u8)
    let advanced ← hash W (toRP W Pr R h B outputs x w hN s).1 (PV_RunJoin_TranscriptRequests51.message absorbed 2#u8)
    ok (core.result.Result.Ok b,({state:=advanced,hash:=hash W (toRP W Pr R h B outputs x w hN s).1,next_row:=U8.wrapping_add (row i) 1#u8} : host_wire.SemanticTranscript _)))=_
  rw [ha]
  simp only [bind_tc_ok]
  erw [PV_RunJoin_CommonSemanticReads51.squeeze W Pr R N hN h B outputs x w hin hc s hcoll hpub k i]
  simp only [bind_tc_ok]
  erw [PV_RunJoin_CommonSemanticReads51.advance W Pr R N hN h B outputs x w hin hc s hcoll hpub k i]
  rfl
#print axioms complete
end R1Z.PV_RunJoin_CommonSemanticBlock51
