import R1Z.PV_RunJoin_CommonOpeningReads51
import R1Z.PV_RunJoin_TranscriptReseed51
import R1Z.PV_RunJoin_TranscriptDigest51
import R1Z.PV_RunJoin_OriginalOpeningFrames51
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_CommonReseed51
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
include hin hc hcoll hpub

theorem frame (r : Rec) (tag : r.rest.vtag=2) :
    ProverRwOuterFrames.flatten (PV_RunJoin_TranscriptReseedSource51.request
      (block (r.tr (.advS 26))) (ProverRwOuterTag.byte .S2))=addr .reseed r := by
  rw [PV_RunJoin_TranscriptReseed51.frame,PV_RunJoin_OpeningByteCodec51.bytes]
  change (openDomain++[2]++LensR1.ans (r.tr (.advS 26)))=(openDomain++[r.rest.vtag]++LensR1.ans (r.tr (.advS 26)))
  rw [tag]

theorem complete (base : ExternalTypes) (heap : Heap) (box : Box) (ops : @ExternalFuns (types base))
    (k : Fin N) (tag : W.vtag=2) :
    @host_transcript.Transcript.new (types base) (selected base heap box ops) _
      (@aspis_core.digest.LegacyHashFn.Insts.Aspis_coreDigestDigest32 (types base) (selected base heap box ops))
      (hash W (toRP W Pr R h B outputs x w hN s).1) (block ((s k).2.1 (.inl (.advS 26)))) .S2=
      ok ({state:=block ((s k).2.1 (.inl .reseed)),
        hash:=hash W (toRP W Pr R h B outputs x w hN s).1} : host_transcript.Transcript _) := by
  rw [PV_RunJoin_TranscriptReseed51.source]
  have req := PV_RunJoin_CommonOracle51.read W Pr R N hN h B outputs x w hin hc s hcoll hpub k .reseed _
    ((frame (record W Pr h B outputs x w (s k).2.1) tag).trans
      (PV_RunJoin_CommonRecord51.address W Pr h B outputs x w R N hN s k .reseed))
  erw [req]
  rfl
#print axioms frame
#print axioms complete
end R1Z.PV_RunJoin_CommonReseed51
