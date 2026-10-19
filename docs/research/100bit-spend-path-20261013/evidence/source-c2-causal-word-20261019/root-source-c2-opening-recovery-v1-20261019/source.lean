import RawSourceC2CutBinding
import RawSourceDigestLog

/-! Instantiate pre-commitment recovery at the actual source C2 frame and
its own parsed root. Source-log containment and actual accepted opening reads
remain explicit; no per-opening root/frame or pre-commitment premise is given. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1PublicPreparation.RawSourceC2OpeningRecovery
open Aeneas Aeneas.Std Result AspisR1
open FS FS2 FS2.Duplex
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.SqueezeOracleBridge
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open Merkle32Path Merkle32Leaf MerkleTable MerkleLeafRecovery MerkleRecordedLog

/-- The lightweight log used by the global-oracle bridge is exactly the
same actual call log used by the commitment-frame theorem. -/
theorem sourceLog_eq {Hash : Type} {D : aspis_core.Digest32 Hash} {pre : r1_wire.Prefix}
    (cs : List (SourceFull25.Call D pre)) :
    SourceDigestLog.sourceLog cs = RawSourceC2CutBinding.sourceLog cs := rfl

theorem all_c2_openings_recovered_before_actual_frame
    {Hash : Type} {D : aspis_core.Digest32 Hash} {pre : r1_wire.Prefix}
    (values : SemanticPrefixCodec.Full)
    (hfull : SemanticPrefixCodec.encodeFull values = PrefixAdapter.completedRecords pre)
    (cs : List (SourceFull25.Call D pre))
    (hrows : cs.map (fun c => c.row.val) = List.range 25)
    (iv : State) (H : Bytes → State) (tr : List (Bytes × State)) (Q : Nat)
    (hsource : SourceDigestLog.sourceLog cs ⊆ tr)
    (hcons : ∀ q ∈ tr, q.2 = H q.1) (hQ : firstReads emptyTable tr ≤ Q)
    (hout : ¬ hitsBad (AllAddressCollision.bad iv RawByteCollisionTargets.pred Q) emptyTable tr) :
    ∃ c ∈ cs, c.row.val = 2 ∧
      let root := SemanticPayloadView.rootAt2 values
      let frame := CommitmentRootFrames.c2Frame (decodeState c.before.state) root
      Read tr frame ∧
      ∀ (packed salt : Bytes), packed.length = 128 → salt.length = 32 →
        ∀ (slots : List (Fin 8)) (path : Path slots),
          (eval H (MerkleProgram.leafProgram path (leafInput 0xf1 packed salt))).2 = root →
          (∀ a, Read (eval H (MerkleProgram.leafProgram path
            (leafInput 0xf1 packed salt))).1 a → Read tr a) →
          RawByteCutStability.recoverAt 0xf1 128 (RawByteCutRecovery.cut tr frame)
            slots root = some (packed,salt) := by
  obtain ⟨c,hc,hrow,hframe,hpred⟩ :=
    RawSourceC2CommitmentFrame.full25_has_c2_target values hfull cs hrows
  have hsourceOld : RawSourceC2CutBinding.sourceLog cs ⊆ tr := by
    rw [← sourceLog_eq cs]
    exact hsource
  have hmem := hsourceOld (RawSourceC2CutBinding.sourceLog_absorb_mem cs c hc)
  have hread : Read tr (CommitmentRootFrames.c2Frame
      (decodeState c.before.state) (SemanticPayloadView.rootAt2 values)) :=
    List.mem_map.mpr ⟨_,hmem,hframe⟩
  refine ⟨c,hc,hrow,hread,?_⟩
  intro packed salt hw hs slots path haccept hopen
  apply RawByteCutRecovery.recover_at_first_commitment iv H tr Q hcons hQ hout
    0xf1 128 packed salt hw hs path (SemanticPayloadView.rootAt2 values) _ 8 hread
    _ haccept hopen
  rw [← hframe]
  exact hpred

#print axioms sourceLog_eq
#print axioms all_c2_openings_recovered_before_actual_frame
end AspisR1PublicPreparation.RawSourceC2OpeningRecovery
end
