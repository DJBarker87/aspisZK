import R1Z.PV_RunJoin_CommonSemanticBlock51
import R1Z.PV_RunJoin_SemanticSampler51
import R1Z.PV_RunJoin_SemanticDigest51
import R1Z.PV_RunJoin_SemanticFrames51
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_CommonSemanticSource51
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
    (k : Fin N) (i : Fin 27) (small : i.val<25) (framed : Slice U8)
    (hp : framed.val.map ProverCommitOwnerBytes42.byte=(record W Pr h B outputs x w (s k).2.1).rest.framed i) :
    let self : host_wire.SemanticTranscript aspis_core.digest.LegacyHashFn :=
      ⟨block (fieldVal (fc (.absS i)) (record W Pr h B outputs x w (s k).2.1)),
        hash W (toRP W Pr R h B outputs x w hN s).1,row i⟩
    let next : host_wire.SemanticTranscript aspis_core.digest.LegacyHashFn :=
      ⟨block ((s k).2.1 (.inl (.advS i))),hash W (toRP W Pr R h B outputs x w hN s).1,
        U8.wrapping_add (row i) 1#u8⟩
    ∃ q : ProverRwFull.aspis_core.field.QM31,
      ProverCommitSubfieldOps47.Canonical (PV_RunJoin_SemanticScalar50.raw q) ∧
      ProverCommitValueRange47.embed (AspisR1.ExtractedCurrentQM31Exact.decode (PV_RunJoin_SemanticScalar50.raw q))=
        PhaseSamplerParserBin.scalar ((s k).2.1 (.inl (.sqS i))) ∧
      @host_wire.SemanticTranscript.semantic (types base) (selected base heap box ops) _
        (@aspis_core.digest.LegacyHashFn.Insts.Aspis_coreDigestDigest32 (types base) (selected base heap box ops))
        self (row i) framed=(do
          let parsed ← @host_wire.parse_record (types base) (selected base heap box ops) (row i) framed
          match parsed with
          | .Err e => ok (core.result.Result.Err e,self)
          | .Ok _ => ok (core.result.Result.Ok q,next)) := by
  dsimp only
  obtain ⟨q,hq,hc,hmodel⟩ := PV_RunJoin_SemanticSampler51.complete base heap box ops ((s k).2.1 (.inl (.sqS i)))
  refine ⟨q,hc,hmodel,?_⟩
  have bound : ¬ row i > 24#u8 := by change ¬24<i.val;omega
  unfold host_wire.SemanticTranscript.semantic host_wire.SemanticTranscript.sample_block
  simp only [if_neg bound,bne_self_eq_false,Bool.false_eq_true,if_false]
  cases run : @host_wire.parse_record (types base) (selected base heap box ops) (row i) framed with
  | fail e => rfl
  | div => rfl
  | ok status =>
    cases status with
    | Err e => rfl
    | Ok payload =>
      simp only [bind_tc_ok,core.result.Result.Insts.CoreOpsTry.branch]
      rw [PV_RunJoin_CommonSemanticBlock51.complete W Pr R N hN h B outputs x w hin hc s hcoll hpub base heap box ops k i framed hp]
      simp only [bind_tc_ok,Aeneas.Std.uncurry,core.result.Result.Insts.CoreOpsTry.branch]
      rw [hq]
      rfl
#print axioms complete
end R1Z.PV_RunJoin_CommonSemanticSource51
