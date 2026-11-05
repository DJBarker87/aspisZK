import NIN_Cuts
import NIB_ReadToSettlement
set_option autoImplicit false
noncomputable section
namespace AspisR1.NIN_PhysicalInstance
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

/-- Universal conditional model instance on the SAME response-selected entries.
No freely chosen Cuts, history equality, carrier equality, or recorder is an input.
The Pool-entry projection is an OPEN native association, not an accepted trust row.
The entry-association binder also maps the SAME Pool invocation to game u. -/
theorem physical_instance {Tx W : Type}
    (Q : Nat) (bound : ART_AdversaryWork.work cfg hashv copy allocator id a H ≤ Q)
    (reached : ((eval H source).2).2.2.isSome = true)
    (prepared : CheckpointBytes5Writer.Prepared) (accumulator : CheckpointBytes5Writer.Accumulator)
    (domain : NGC_KNE_Caller.WriterDomain prepared accumulator)
    (hp hu hc : CheckpointBytes5Effect.Digest)
    (p : CPG_Projection.Observations Tx A) (t u : Tx)
    (n1 : S2W_ExtractionBoundary.First) (n2 : S2W_ExtractionBoundary.Second)
    (actions : List (CPP_BankState.Action A)) (std : S2W_TrustedStd.TrustedStd copy)
    (valid1 : Valid (((eval H source).2).1.entry).heap) (system : S2W_ExtractionBoundary.Program)
    (final1 : A) (post1 : Heap (Nat → Record))
    (game : CPH_Game.DeployedPairExecution p t u (((eval H source).2).1.entry) ((((eval H source).2).2.2.get reached).1.entry)
      (NGR_HISTORY.checkpoint prepared accumulator domain hp hu hc) actions n1 n2 copy allocator id)
    (native_writer_result : first n1 copy allocator (((eval H source).2).1.entry) id ((eval H source).2).1.data ((eval H source).2).1.state =
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
      s.pub s.proof s.checkpoint () none = ok (.Ok ()))
    {Invocation Context Key RuntimeState Accounts Other LaneImage : Type} [DecidableEq Key]
    (runtime : NGK_NFO_PoolReturnData.Runtime Context Key RuntimeState)
    (law : NGK_NFR_PoolReturnData.RuntimeReturnData runtime)
    (emitInvocation poolInvocation : Invocation) (context : Invocation → Context)
    (program : Invocation → Key) (selected : Key) (readState : RuntimeState)
    (state after : AspisR1.S2I.ReturnData.State Accounts Other)
    (emittedStatement : NFY_NEU_EmitModel.Statement)
    (sameCpi : poolInvocation = emitInvocation)
    (selectedProgram : program emitInvocation = selected)
    (noInterveningCpi : readState = runtime.write (context emitInvocation)
      (program emitInvocation) (AspisR1.S2K.ResultPayload.bytes emittedStatement).val)
    (emitted : AspisR1.NFY_JHb_Emit.source
      (fun st bytes => ok (AspisR1.S2I.ReturnData.set st bytes)) state emittedStatement = ok (.Ok after))
    (authenticated : NGK_NFO_ReadModel.Accepted) (events : List NGK_NFO_ReadModel.Event)
    (acceptedDecoder : NGK_NFO_ReadModel.run selected (.Ok ())
      (runtime.read (context poolInvocation) readState) NGK_NFO_PacketDecoder.run =
      ok (.Ok authenticated,events))
    (validate : NGK_NFR_CSettlement.Output → Result (core.result.Result Unit NGK_NFR_CSettlement.Error))
    (lane : NGK_NFR_CSettlement.Output → Result (core.result.Result LaneImage NGK_NFR_CSettlement.Error))
    (image : LaneImage)
    (checked : validate authenticated.value = ok (.Ok ()))
    (advanced : lane authenticated.value = ok (.Ok image))
    (verifierEntry : Invocation → Entry)
    (sameVerifierEntry : verifierEntry emitInvocation =
      (((eval H source).2).2.2.get reached).1.entry) :
    (NGP_L159.L159_statement p t u
      (NIN_Cuts.of_producers f s
        prepared accumulator domain hp hu hc emittedStatement authenticated)
      Q (eval H (Hiq_RecordedJoint.program source ARQ_Observer.project
        (ARQ_Observer.select cfg id)))) ∧
    verifierEntry poolInvocation = CPG_Projection.entry p u := by
  let cuts := NIN_Cuts.of_producers f s
    prepared accumulator domain hp hu hc emittedStatement authenticated
  obtain ⟨adjacent,keys,parent,copied,size,loaded,buffer,_,_,_⟩ :=
    NGR_HISTORY.saved_to_loaded prepared accumulator domain hp hu hc p t u
      ((eval H source).2).1.entry (((eval H source).2).2.2.get reached).1.entry
      actions n1 n2 copy std allocator valid1 id system ((eval H source).2).1.data ((eval H source).2).1.state final1 post1
      game native_writer_result protection ordinary RuntimePersistence L sdk w2 related2 valid2
  have checkpoint := NGS_CHECKPOINT.loaded_read (((eval H source).2).2.2.get reached).1.entry
    ops s.checkpointAccount s.checkpoint (NGR_HISTORY.checkpoint prepared accumulator domain hp hu hc)
    checkpoint2Index checkpoint2Read buffer
  have history : NGP_L159.History_statement p t u cuts :=
    ⟨adjacent,keys,parent,copied,size,loaded,checkpoint⟩
  have carriers := NGS_CARRIERS.saved_to_carriers base err r hashv copy allocator a H
    Q bound reached prepared accumulator domain hp hu hc p t u n1 n2 actions std valid1
    system ((eval H source).2).1.data ((eval H source).2).1.state final1 post1 game native_writer_result protection ordinary
    RuntimePersistence L sdk w2 related2 valid2 f s finish1 proof1Index public1Index
    proof1Read public1Read range1 length1 proof2Index proof2Read range2 length2
    v validation encoding writerResult checkpoint2Index checkpoint2Read readerResult
  have pool := NIB_ReadToSettlement.read_to_settlement runtime law emitInvocation poolInvocation
    context program selected readState state after emittedStatement sameCpi selectedProgram
    noInterveningCpi emitted authenticated events acceptedDecoder validate lane image checked advanced
  exact ⟨⟨history,NIN_Cuts.carrier_or_collision f s
    prepared accumulator domain hp hu hc
    emittedStatement authenticated Q _ carriers pool.2.2.2.2.1 pool.2.2.2.1⟩,
    (congrArg verifierEntry sameCpi).trans (sameVerifierEntry.trans game.consecutive.2.2)⟩

#print axioms physical_instance
end
end AspisR1.NIN_PhysicalInstance
end
