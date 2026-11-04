import NGS_Carriers
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

/-- Direct NGR -> carrier composition on the response-selected entries.
The loaded-byte equality is a CONCLUSION of NGR, never an input here. Native
writer, source protection, ordinary account and SDK domains remain explicit. -/
theorem saved_to_carriers {Tx W : Type}
    (Q : Nat) (bound : ART_AdversaryWork.work cfg hashv copy allocator id a H ≤ Q)
    (reached : ((eval H source).2).2.2.isSome = true)
    (prepared : CheckpointBytes5Writer.Prepared) (accumulator : CheckpointBytes5Writer.Accumulator)
    (domain : NGC_KNE_Caller.WriterDomain prepared accumulator)
    (hp hu hc : CheckpointBytes5Effect.Digest)
    (p : CPG_Projection.Observations Tx A) (t u : Tx)
    (n1 : S2W_ExtractionBoundary.First) (n2 : S2W_ExtractionBoundary.Second)
    (actions : List (CPP_BankState.Action A)) (std : S2W_TrustedStd.TrustedStd copy)
    (valid1 : Valid (((eval H source).2).1.entry).heap) (system : S2W_ExtractionBoundary.Program)
    (data1 : Slice U8) (state1 final1 : A) (post1 : Heap (Nat → Record))
    (game : CPH_Game.DeployedPairExecution p t u (((eval H source).2).1.entry) ((((eval H source).2).2.2.get reached).1.entry)
      (NGR_HISTORY.checkpoint prepared accumulator domain hp hu hc) actions n1 n2 copy allocator id)
    (native_writer_result : first n1 copy allocator (((eval H source).2).1.entry) id data1 state1 =
      ok (.Ok ((NGR_HISTORY.checkpoint prepared accumulator domain hp hu hc),post1,final1)))
    (protection : CPH_Protection.Facts p t
      (NGR_HISTORY.checkpoint prepared accumulator domain hp hu hc) id)
    (ordinary : CPG_Projection.ordinary p system t ((p.layout t).handles 2).1)
    (RuntimePersistence : CPR_DataPersistence.TwoTransactionLaw
      (CPG_Projection.adjacent p) (CPG_Projection.ordinary p system)
      (CPG_Projection.before p) (CPG_Projection.tentative p)
      (CPG_Projection.success p) (CPG_Projection.loaded p))
    (L : Library W (Nat → Record)) (sdk : S2TrustedSdkBorrow L)
    (w2 : W) (related2 : L.related w2 ((((eval H source).2).2.2.get reached).1.entry).heap) (valid2 : Valid ((((eval H source).2).2.2.get reached).1.entry).heap)
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
    (writerResult : AdapterRw.first_decoded ops f.semantic f.pub f.proof f.split = ok (.Ok (NGR_HISTORY.checkpoint prepared accumulator domain hp hu hc)))
    (checkpoint2Index : Slice.index_usize ((((eval H source).2).2.2.get reached).1.entry.second secondSizes)
      6#usize = ok s.checkpointAccount)
    (checkpoint2Read : AdapterRw.r1_pool_adapter.owned.OwnedAccount.data ops s.checkpointAccount =
      ok (.Ok s.checkpoint))
    (readerResult : (ops).op11 (AdapterRw.SolanaDigest.Insts.Aspis_coreDigestDigest32 ops)
      s.pub s.proof s.checkpoint () none = ok (.Ok ())) :
    (bytesOf s.proof.val = bytesOf f.proof.val ∧ bytesOf s.pub.val = bytesOf f.pub.val) ∨
    BinRawByteCollisionTargets.event SelectedTranscriptParams.params.iv (Q+2965)
      (eval H (Hiq_RecordedJoint.program source ARQ_Observer.project
        (ARQ_Observer.select cfg id))) := by
  obtain ⟨_,_,_,_,_,_,loaded,_,_,_⟩ := NGR_HISTORY.saved_to_loaded
    prepared accumulator domain hp hu hc p t u (((eval H source).2).1.entry) ((((eval H source).2).2.2.get reached).1.entry) actions n1 n2 copy std
    allocator valid1 id system data1 state1 final1 post1 game native_writer_result
    protection ordinary RuntimePersistence L sdk w2 related2 valid2
  exact same_inputs_or_collision base err r hashv copy allocator a H Q bound
    reached f s finish1 proof1Index public1Index proof1Read public1Read range1 length1
    proof2Index proof2Read range2 length2 v validation encoding
    (NGR_HISTORY.checkpoint prepared accumulator domain hp hu hc) writerResult
    checkpoint2Index checkpoint2Read loaded readerResult

#print axioms saved_to_carriers
end
end AspisR1.NGS_CARRIERS
end
