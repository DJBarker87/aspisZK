import R1Z.PV_RunJoin_CommonSemanticBlock51
import R1Z.PV_RunJoin_CircleInstalledTotal55
import R1Z.PV_RunJoin_SemanticDigest51
import R1Z.PV_RunJoin_SemanticFrames51
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_CommonCircleFirst55
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
    (k : Fin N) (framed : Slice U8)
    (hp : framed.val.map ProverCommitOwnerBytes42.byte=(record W Pr h B outputs x w (s k).2.1).rest.framed ⟨25,by decide⟩) :
    let selectedOps := @PV_RunJoin_CircleNeutralSelected52.selected (types base) ops
    let self : host_wire.SemanticTranscript aspis_core.digest.LegacyHashFn :=
      ⟨block (fieldVal (fc (.absS ⟨25,by decide⟩)) (record W Pr h B outputs x w (s k).2.1)),
        hash W (toRP W Pr R h B outputs x w hN s).1,25#u8⟩
    let next : host_wire.SemanticTranscript aspis_core.digest.LegacyHashFn :=
      ⟨block ((s k).2.1 (.inl (.advS ⟨25,by decide⟩))),hash W (toRP W Pr R h B outputs x w hN s).1,26#u8⟩
    ∃ q : aspis_core.circle.SecureCirclePoint,
      ProverCommitSubfieldOps47.Canonical (PV_RunJoin_SemanticScalar50.raw q.x) ∧
      ProverCommitSubfieldOps47.Canonical (PV_RunJoin_SemanticScalar50.raw q.y) ∧
      PV_RunJoin_CircleInstalledExact55.coordinates q=
        (PhaseSamplerParserBin.circle ⟨0,by decide⟩ ((s k).2.1 (.inl (.sqS ⟨25,by decide⟩)))).1 ∧
      @host_wire.SemanticTranscript.challenge_reference_circle_point (types base) (selected base heap box selectedOps) _
        (@aspis_core.digest.LegacyHashFn.Insts.Aspis_coreDigestDigest32 (types base) (selected base heap box selectedOps))
        self 25#u8 framed=(do
          let parsed ← @host_wire.parse_record (types base) (selected base heap box selectedOps) 25#u8 framed
          match parsed with
          | .Err e => ok (core.result.Result.Err e,self)
          | .Ok _ => ok (core.result.Result.Ok q,next)) := by
  dsimp only
  let selectedOps := @PV_RunJoin_CircleNeutralSelected52.selected (types base) ops
  obtain ⟨q,hq,hx,hy,hmodel⟩ := PV_RunJoin_CircleInstalledTotal55.complete base heap box ops
    (block ((s k).2.1 (.inl (.sqS ⟨25,by decide⟩)))) .First
  have model : PV_RunJoin_CircleInstalledExact55.coordinates q=
      (PhaseSamplerParserBin.circle ⟨0,by decide⟩ ((s k).2.1 (.inl (.sqS ⟨25,by decide⟩)))).1 := by
    simpa only [PV_RunJoin_CircleNeutralSelected52.row,Bool.false_eq_true,if_false,
      PhaseSamplerParserBin.circle,PhaseCircleBlocksBin.select,PhaseCircleBlocksBin.first,
      PV_RunJoin_OpeningSampler50.block,AspisV8R19.SqueezeOracleBridge.state_roundtrip] using hmodel
  refine ⟨q,hx,hy,model,?_⟩
  unfold host_wire.SemanticTranscript.challenge_reference_circle_point host_wire.SemanticTranscript.sample_block
  simp only [bne_self_eq_false,Bool.false_eq_true,if_false]
  cases run : @host_wire.parse_record (types base) (selected base heap box selectedOps) 25#u8 framed with
  | fail e => rfl
  | div => rfl
  | ok status =>
    cases status with
    | Err e => rfl
    | Ok payload =>
      simp only [bind_tc_ok,core.result.Result.Insts.CoreOpsTry.branch]
      rw [PV_RunJoin_CommonSemanticBlock51.complete W Pr R N hN h B outputs x w hin hc s hcoll hpub base heap box selectedOps k ⟨25,by decide⟩ framed hp]
      simp only [bind_tc_ok,Aeneas.Std.uncurry,core.result.Result.Insts.CoreOpsTry.branch]
      rw [hq]
      rfl
#print axioms complete
end R1Z.PV_RunJoin_CommonCircleFirst55
