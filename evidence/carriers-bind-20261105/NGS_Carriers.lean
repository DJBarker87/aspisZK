import NGS_Selection
import NGS_CheckpointRead
set_option autoImplicit false
noncomputable section
namespace AspisR1.NGS_CARRIERS
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open MultiproofConeCanonical S2W_NativeConsolidation GExq_AccountExperiment
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw SCE_Experiment

section
variable {A C : Type}
    (base : DrvC_Installation.Configuration FIo_Install.W C) (err : C)
    (r : NP6_StdModel.Reservation)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (allocator : Allocator A) (a : Adversary A) (H : Bytes → State)
local notation "cfg" => FIp_Install.configuration err base r
local notation "source" => ART_PartialAccount.account cfg hashv copy allocator CPH_Program.verifier a
local notation "ops" => SCH_IdealSdk.dictionary cfg hashv H
local notation "id" => CPH_Program.verifier

/-- SAME actual source outcome, its response-selected TX2 entry, scanner ranges,
validator/encoder and checkpoint reader/writer observations. The driver must
produce the named observations; no native driver closure is asserted here.
The source, projection and selector in the collision branch are L159/ARX's
literal recorder, fixed before H. No SourceCuts or SameExecution premise. -/
theorem same_inputs_or_collision
    (Q : Nat) (bound : ART_AdversaryWork.work cfg hashv copy allocator id a H ≤ Q)
    (reached : ((eval H source).2).2.2.isSome = true)
    (f : FirstCut) (s : SecondCut) (finish1 : Usize)
    (proof1Index : Slice.index_usize ((eval H source).2).1.entry.first 0#usize = ok f.proofAccount)
    (public1Index : Slice.index_usize ((eval H source).2).1.entry.first 1#usize = ok f.publicAccount)
    (proof1Read : AdapterRw.r1_pool_adapter.owned.OwnedAccount.data ops f.proofAccount = ok (.Ok f.raw))
    (public1Read : AdapterRw.r1_pool_adapter.owned.OwnedAccount.data ops f.publicAccount = ok (.Ok f.pub))
    (range1 : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
      f.raw {start := 688#usize, «end» := finish1} = ok f.proof)
    (length1 : f.raw.val.length = finish1.val)
    (proof2Index : Slice.index_usize ((((eval H source).2).2.2.get reached).1.entry.second secondSizes)
      0#usize = ok s.proofAccount)
    (proof2Read : AdapterRw.r1_pool_adapter.owned.OwnedAccount.data ops s.proofAccount = ok (.Ok s.raw))
    (range2 : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
      s.raw {start := 688#usize, «end» := s.finish} = ok s.proof)
    (length2 : s.raw.val.length = s.finish.val)
    (v : AdapterRw.r1_pool_adapter.ValidatedAsqa)
    (validation : AdapterRw.r1_pool_adapter.owned.validate_asq8 ops id
      ((((eval H source).2).2.2.get reached).1.entry.second secondSizes)
      (((eval H source).2).2.2.get reached).1.data (((eval H source).2).2.2.get reached).1.slot = ok (.Ok v))
    (encoding : (ops).op22 v.statement = ok (.Ok s.encoded))
    (saved : alloc.vec.Vec U8)
    (writerResult : AdapterRw.first_decoded ops f.semantic f.pub f.proof f.split = ok (.Ok saved))
    (checkpoint2Index : Slice.index_usize ((((eval H source).2).2.2.get reached).1.entry.second secondSizes)
      6#usize = ok s.checkpointAccount)
    (checkpoint2Read : AdapterRw.r1_pool_adapter.owned.OwnedAccount.data ops s.checkpointAccount =
      ok (.Ok s.checkpoint))
    (loaded : ((((eval H source).2).2.2.get reached).1.entry.buffers
      ((((eval H source).2).2.2.get reached).1.entry.handles 6).1).val = saved.val)
    (readerResult : (ops).op11 (AdapterRw.SolanaDigest.Insts.Aspis_coreDigestDigest32 ops)
      s.pub s.proof s.checkpoint () none = ok (.Ok ())) :
    (bytesOf s.proof.val = bytesOf f.proof.val ∧ bytesOf s.pub.val = bytesOf f.pub.val) ∨
    BinRawByteCollisionTargets.event SelectedTranscriptParams.params.iv (Q+2965)
      (eval H (Hiq_RecordedJoint.program source ARQ_Observer.project
        (ARQ_Observer.select cfg id))) := by
  have selected := NGS_SELECTION.on_packets ops id ((eval H source).2) reached f s finish1
    proof1Index public1Index proof1Read public1Read range1 length1 proof2Index
    proof2Read range2 length2 v validation encoding
  rw [NGS_SELECTION.ideal_selector base err r hashv H ((eval H source).2)] at selected
  have checkpoint := NGS_CHECKPOINT.loaded_read (((eval H source).2).2.2.get reached).1.entry ops
    s.checkpointAccount s.checkpoint saved checkpoint2Index checkpoint2Read loaded
  have wrote := ARU_FirstHeader.accepted cfg hashv H f.semantic f.pub f.proof f.split saved writerResult
  have read := ARU_SecondHeader.accepted cfg hashv H s.pub s.proof s.checkpoint readerResult
  rw [checkpoint] at read
  have pairs := Option.some.inj (wrote.1.symm.trans read)
  have matched : R9PoolRuntimeBinding.digestMatches H
      ⟨bytesOf f.proof.val,bytesOf f.pub.val⟩ ⟨bytesOf s.proof.val,bytesOf s.pub.val⟩ :=
    ⟨(congrArg Prod.fst pairs).symm,(congrArg Prod.snd pairs).symm⟩
  rcases ARX_LocalCharge.binding source ARQ_Observer.project (ARQ_Observer.select cfg id)
    Q H (ARW_LocalBudget.issued cfg hashv copy allocator id a Q H bound) with bad | binding
  · exact Or.inr bad
  · rw [selected] at binding
    exact Or.inl (binding matched)

#print axioms same_inputs_or_collision
end
end AspisR1.NGS_CARRIERS
end
