import S6CurrentStage1FirstFieldsV1
import S2W_D189Consolidation
set_option autoImplicit false
noncomputable section
namespace AspisS6SdkStage1Reuse
open Aeneas Aeneas.Std Result
open AspisR1 S2Trust S2W_D189Entry S2W_D189Wrappers
open S2W_TrustedStd S2W_WrapperLaws S2W_ReturnedCheckpoint S2W_EntryWriteHistory
open S2W_CommittedCheckpoint
open AspisS6CurrentFirstInstallation AspisS6CurrentVerifierCarrier

/-- A successful actual owned read rules out the deferred snapshot error and
identifies the complete original native public buffer, including its length.
There is no snapshot-shape, length or buffer-identity hypothesis. -/
theorem public_read (e : Entry) (ops : AdapterRw.Ops) (pub : Slice U8)
    (read : AdapterRw.r1_pool_adapter.owned.OwnedAccount.data ops
      (e.snapshot 1 1880 1880) = ok (.Ok pub)) :
    pub = e.buffers (e.handles 1).1 ∧ pub.val.length = 1880 := by
  obtain ⟨copied,stored,view⟩ := S2W.SnapshotJoin.data_success ops
    (e.snapshot 1 1880 1880) pub read
  change (if (e.buffers (e.handles 1).1).val.length = 1880 ∨
      (e.buffers (e.handles 1).1).val.length = 1880 then
      core.result.Result.Ok (e.buffers (e.handles 1).1) else
      core.result.Result.Err AdapterRw.solana_program_error.ProgramError.InvalidAccountData) =
        core.result.Result.Ok copied at stored
  split at stored
  · rename_i admitted
    have same := core.result.Result.Ok.inj stored
    subst copied
    have bytes := congrArg Subtype.val view
    have equal : pub = e.buffers (e.handles 1).1 := Subtype.ext bytes.symm
    refine ⟨equal,?_⟩
    rw [equal]
    exact admitted.elim id id
  · cases stored

/-- ONE accepted composed SDK wrapper, under the existing approved D188/D189
interpretation, supplies the original public account bytes and the concrete
source decoder/codec/first connection. SDK/native eligibility and extraction
are the named standing boundaries; no owned success or caller-input identity
is an additional premise. The actual returned write heap is retained. -/
theorem accepted_sdk_stage1 {W A : Type}
    (L : Library W (Nat → Record)) (sdk : S2TrustedSdkBorrow L)
    (copy : Heap (Nat → Record) → Nat → Payload → Outcome (Nat → Record))
    (std : TrustedStd copy) (allocator : Allocator A)
    (e : Entry) (world : W)
    (admission : S2W_D189Consolidation.RuntimeEntrypointAdmission L e world 3)
    (ops : AdapterRw.Ops) (vops : AspisR1CurrentCaller.Ops)
    (native1 : S2W_ExtractionBoundary.First) (native2 : S2W_ExtractionBoundary.Second)
    (hashv : S2Z.Oracle.Parts → Result S2Z.Oracle.Digest)
    (extraction : S2W_DigestExtraction.AeneasExtraction
      (install ops vops) native1 native2 hashv)
    (program : S2W_ExtractionBoundary.Program) (data : Slice U8)
    (initial final : A) (saved : alloc.vec.Vec U8) (post : Heap (Nat → Record))
    (accepted : S2W_D189Wrappers.first native1 copy allocator e program data initial =
      ok (.Ok (saved,post,final))) :
    post = writeBracket e.heap 2 0 0 (source (nativeBytes saved)) ∧
    ∃ (pub proof : Slice U8) (split : Usize)
      (statement : AspisS6CurrentCodecInstallation.Statement) (encoded : Array U8 1880#usize),
      pub = e.buffers (e.handles 1).1 ∧ pub.val.length = 1880 ∧
      payloadBytes encode (L.cellPayload world (L.accountData world 1))
        (L.cellPayload world (L.accountData world 1)).descriptor.length =
          MultiproofConeCanonical.bytesOf pub.val ∧
      AspisS6CurrentCodecInstallation.decode pub = ok (.Ok statement) ∧
      AspisR1TerminalDecoder.pool_v1.pair_forest_terminal.decode_pool_v1_pair_forest_terminal_statement_v1 pub =
        ok (.Ok (AspisS6CurrentAdapterCarrier.toPoolV1PairForestTerminalStatementV1 statement)) ∧
      AspisS6CurrentCodecInstallation.encode statement = ok (.Ok encoded) ∧ encoded.val = pub.val ∧
      AspisR1CurrentCaller.FirstComposition.firstCurrent
        AdapterRw.solana_program_error.ProgramError.InvalidAccountData vops
        (toDigest (AdapterRw.SolanaDigest.Insts.Aspis_coreDigestDigest32 (install ops vops)))
        (fun error => ops.op44 (fromError error)) pub proof split = ok (.Ok saved) ∧
      S2W_AccountObservations.observe encode e.metadata 3 post 1 =
        S2W_D189Interpretation.nativeObserve L encode e.metadata 3 world e.heap.ambient 1 := by
  obtain ⟨native,written⟩ := S2W_D189Wrappers.first_accepted native1 copy std allocator
    e program data initial final saved post accepted
  have owned : AdapterRw.r1_pool_adapter.owned.stage1_owned (install ops vops)
      program e.first data = ok (.Ok saved) :=
    (extraction.stage1 program e.first data).symm.trans native
  obtain ⟨pa,pu,pub,raw,statement,semantic,proof,split,start,finish,encoded,
    ip,iu,rp,ru,decoded,nativeDecode,encodedCall,sameBytes,valid,selected,ranged,tx1,length,first⟩ :=
    AspisS6CurrentStage1FirstFields.accepted_stage1 ops vops program e.first data saved owned
  have sameAccount := Result.ok.inj (iu.symm.trans (first_index e).2.1)
  subst pu
  obtain ⟨buffer,size⟩ := public_read e (install ops vops) pub ru
  have observed := native_buffer e L sdk world admission.related admission.entry.valid 1
  rw [← buffer] at observed
  have disjoint := first_disjoint e (install ops vops) program data saved owned
  have frame := S2W_AccountObservations.write_frame encode e.metadata 3 e.heap 2 0 0
    (source (nativeBytes saved)) rfl rfl 1 (fun _ => disjoint 1 (by decide) (by decide))
  have initialObservation := S2W_D189Interpretation.native_observation L sdk encode e.metadata 3
    world e.heap admission.related admission.entry.valid
  refine ⟨written,pub,proof,split,statement,encoded,buffer,size,observed,decoded,nativeDecode,
    encodedCall,sameBytes,first,?_⟩
  rw [written]
  exact frame.trans ((congrFun initialObservation 1).symm)

#print axioms public_read
#print axioms accepted_sdk_stage1
end AspisS6SdkStage1Reuse
