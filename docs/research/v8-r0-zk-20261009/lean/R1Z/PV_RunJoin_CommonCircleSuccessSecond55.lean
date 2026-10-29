import R1Z.PV_RunJoin_CommonCircleSecond55
import R1Z.PV_RunJoin_CircleResultSuccess55
import R1Z.PV_RunJoin_CommonSemanticBlock51
import R1Z.PV_RunJoin_CircleTapeSecond55
import R1Z.PV_RunJoin_CommonCircleBlockSecond55
import R1Z.PV_RunJoin_CircleSourceRows55
import R1Z.PV_RunJoin_SemanticDigest51
import R1Z.PV_RunJoin_SemanticFrames51
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_CommonCircleSuccessSecond55
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
set_option allowUnsafeReducibility true in
attribute [local irreducible] ProverRwP6BoundaryInstall.selected
attribute [local irreducible] selected PV_B2_F_RawNative.selected PV_B2_F_ResourceFamilies.selected
include hin hc hcoll hpub

theorem complete (base : ExternalTypes) (heap : Heap) (box : Box) (ops : @ExternalFuns (types base))
    (k : Fin N) (framed : Slice U8)
    (hp : framed.val.map ProverCommitOwnerBytes42.byte=(record W Pr h B outputs x w (s k).2.1).rest.framed ⟨26,by decide⟩)
    (point : aspis_core.circle.SecureCirclePoint) (next : host_wire.SemanticTranscript aspis_core.digest.LegacyHashFn)
    (success : @host_wire.SemanticTranscript.challenge_reference_circle_point (types base)
      (selected base heap box (@PV_RunJoin_CircleNeutralSelected52.selected (types base) ops)) _
      (@aspis_core.digest.LegacyHashFn.Insts.Aspis_coreDigestDigest32 (types base)
        (selected base heap box (@PV_RunJoin_CircleNeutralSelected52.selected (types base) ops)))
      ⟨block (fieldVal (fc (.absS ⟨26,by decide⟩)) (record W Pr h B outputs x w (s k).2.1)),hash W (toRP W Pr R h B outputs x w hN s).1,26#u8⟩ 26#u8 framed=ok (.Ok point,next)) :
    ProverCommitSubfieldOps47.Canonical (PV_RunJoin_SemanticScalar50.raw point.x) ∧
    ProverCommitSubfieldOps47.Canonical (PV_RunJoin_SemanticScalar50.raw point.y) ∧
    PV_RunJoin_CircleInstalledExact55.coordinates point=
      (PhaseSamplerParserBin.circle ⟨1,by decide⟩ ((s k).2.1 (.inl (.sqS ⟨26,by decide⟩)))).1 ∧
    next.state=block ((s k).2.1 (.inl (.advS ⟨26,by decide⟩))) ∧
    next.hash=hash W (toRP W Pr R h B outputs x w hN s).1 ∧ next.next_row=27#u8 := by
  obtain ⟨q,hx,hy,hm,heq⟩ := PV_RunJoin_CommonCircleSecond55.complete W Pr R N hN h B outputs x w hin hc s hcoll hpub base heap box ops k framed hp
  dsimp only at heq
  rw [heq] at success
  have same := PV_RunJoin_CircleResultSuccess55.complete _ _ _ _ _ _ success
  rcases same with ⟨hpoint,hnext⟩
  rw [hpoint,hnext]
  exact ⟨hx,hy,hm,rfl,rfl,rfl⟩
#print axioms complete
end R1Z.PV_RunJoin_CommonCircleSuccessSecond55
