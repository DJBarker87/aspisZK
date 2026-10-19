import RawSourceC2CommitmentFrame
import RawByteCutStability

/-! Reuse the existing simultaneous commitment-cut stability theorem at the
actual source C2 frame. The global execution-log embedding, consistency,
query bound and single collision exclusion remain explicit. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1PublicPreparation.RawSourceC2CutBinding
open Aeneas Aeneas.Std Result
open AspisR1
open FS FS2 FS2.Duplex
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.SqueezeOracleBridge
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open SourceDigestAddresses

/-- Three actual digest input/output pairs retained by a source call. -/
def callLog {H : Type} {D : aspis_core.Digest32 H} {pre : r1_wire.Prefix}
    (c : SourceFull25.Call D pre) : List (Bytes × State) :=
  [(flatten (TranscriptStep.absorbParts c.before.state c.tag c.record.framed), decodeState c.absorbed),
   (flatten (TranscriptStep.readParts c.absorbed 1#u8), decodeState c.block),
   (flatten (TranscriptStep.readParts c.absorbed 2#u8), decodeState c.state)]

def sourceLog {H : Type} {D : aspis_core.Digest32 H} {pre : r1_wire.Prefix}
    (cs : List (SourceFull25.Call D pre)) : List (Bytes × State) := cs.flatMap callLog

theorem callLog_actual {H : Type} {D : aspis_core.Digest32 H} {pre : r1_wire.Prefix}
    (c : SourceFull25.Call D pre) (q : Bytes × State) (hq : q ∈ callLog c) :
    ∃ input : Slice (Slice U8), ∃ output : TranscriptStep.Bytes32,
      q = (flatten input,decodeState output) ∧ D.digest c.before.hash input = .ok output := by
  simp only [callLog,List.mem_cons,List.not_mem_nil,or_false] at hq
  rcases hq with rfl | rfl | rfl
  · exact ⟨_,_,rfl,c.absorb⟩
  · exact ⟨_,_,rfl,c.read1⟩
  · exact ⟨_,_,rfl,c.read2⟩

theorem sourceLog_length {H : Type} {D : aspis_core.Digest32 H} {pre : r1_wire.Prefix}
    (cs : List (SourceFull25.Call D pre)) : (sourceLog cs).length = 3 * cs.length := by
  induction cs with
  | nil => rfl
  | cons c cs ih => simp [sourceLog,callLog,List.flatMap_cons] at ih ⊢; omega

theorem sourceLog_absorb_mem {H : Type} {D : aspis_core.Digest32 H} {pre : r1_wire.Prefix}
    (cs : List (SourceFull25.Call D pre)) (c : SourceFull25.Call D pre) (hc : c ∈ cs) :
    (flatten (TranscriptStep.absorbParts c.before.state c.tag c.record.framed),
      decodeState c.absorbed) ∈ sourceLog cs := by
  exact List.mem_flatMap.mpr ⟨c,hc,by simp [callLog]⟩

/-- One actual row2 digest call supplies the exact read/target gates consumed
by the old cut theorem. No recovered word or per-path premise is supplied. -/
theorem c2_cut_stable {Hash : Type} {D : aspis_core.Digest32 Hash} {pre : r1_wire.Prefix}
    (values : SemanticPrefixCodec.Full)
    (hfull : SemanticPrefixCodec.encodeFull values = PrefixAdapter.completedRecords pre)
    (cs : List (SourceFull25.Call D pre))
    (hrows : cs.map (fun c => c.row.val) = List.range 25)
    (iv : State) (H : Bytes → State) (tr : List (Bytes × State)) (Q : Nat)
    (hsource : sourceLog cs ⊆ tr)
    (hcons : ∀ q ∈ tr, q.2 = H q.1)
    (hQ : firstReads emptyTable tr ≤ Q)
    (hout : ¬ hitsBad (AllAddressCollision.bad iv RawByteCollisionTargets.pred Q) emptyTable tr) :
    ∃ c ∈ cs, c.row.val = 2 ∧
      let frame := CommitmentRootFrames.c2Frame (decodeState c.before.state) (SemanticPayloadView.rootAt2 values)
      Read tr frame ∧
      (fun slots => RawByteCutStability.recoverAt 0xf1 128 (RawByteCutRecovery.cut tr frame)
        slots (SemanticPayloadView.rootAt2 values)) =
      (fun slots => RawByteCutStability.recoverAt 0xf1 128 tr slots (SemanticPayloadView.rootAt2 values)) := by
  obtain ⟨c,hc,hrow,hframe,hpred⟩ :=
    RawSourceC2CommitmentFrame.full25_has_c2_target values hfull cs hrows
  have hmem := hsource (sourceLog_absorb_mem cs c hc)
  have hread : Read tr
      (CommitmentRootFrames.c2Frame (decodeState c.before.state) (SemanticPayloadView.rootAt2 values)) := by
    exact List.mem_map.mpr ⟨_,hmem,hframe⟩
  refine ⟨c,hc,hrow,hread,?_⟩
  apply RawByteCutStability.all_paths_stable iv H tr Q hcons hQ hout
    0xf1 128 (SemanticPayloadView.rootAt2 values) _ 8 hread
  rw [← hframe]
  exact hpred

#print axioms callLog_actual
#print axioms sourceLog_length
#print axioms c2_cut_stable
end AspisR1PublicPreparation.RawSourceC2CutBinding
end
