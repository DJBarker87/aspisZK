import S6SdkStage1ReuseFactoredV1
import S6SdkSourceCutReuseV1
set_option autoImplicit false
noncomputable section
namespace AspisS6SdkEnclosingCuts
open Aeneas Aeneas.Std Result
open AspisR1 S2Trust S2W_D189Entry S2W_D189Wrappers S2W_TrustedStd
open S2W_WrapperLaws S2W_ReturnedCheckpoint S2W_EntryWriteHistory S2W_CommittedCheckpoint
open S2W_NativeConsolidation AspisS6CurrentFirstInstallation AspisS6CurrentVerifierCarrier
open AspisS6CurrentCodecInstallation AspisS6CurrentAdapterCarrier
/-- One complete SDK wrapper acceptance supplies S6 reuse for EVERY published
SourceCuts witness of that same execution. Caller-cut/input/semantic identity
is not an additional enclosing premise. Standing interpretation stays explicit. -/
theorem accepted_sdk_all_cuts {W A : Type}
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
    S2W_AccountObservations.observe S2W_ReturnedCheckpoint.encode e.metadata 3 post 1 =
      S2W_D189Interpretation.nativeObserve L S2W_ReturnedCheckpoint.encode e.metadata 3 world e.heap.ambient 1 ∧
    ∀ (accounts2 : Slice AdapterRw.Cuts.Account) (f : FirstCut) (s : SecondCut),
      SourceCuts (install ops vops) e.first accounts2 saved f s →
      f.pub = e.buffers (e.handles 1).1 ∧ f.pub.val.length = 1880 ∧
      payloadBytes S2W_ReturnedCheckpoint.encode (L.cellPayload world (L.accountData world 1))
        (L.cellPayload world (L.accountData world 1)).descriptor.length =
          MultiproofConeCanonical.bytesOf f.pub.val ∧
      ∃ encoded,
        decode f.pub = ok (.Ok f.statement) ∧
        AspisR1TerminalDecoder.pool_v1.pair_forest_terminal.decode_pool_v1_pair_forest_terminal_statement_v1 f.pub =
          ok (.Ok (toPoolV1PairForestTerminalStatementV1 f.statement)) ∧
        AspisS6CurrentCodecInstallation.encode f.statement = ok (.Ok encoded) ∧ encoded.val = f.pub.val ∧
        f.split = AspisR1CurrentCaller.compact.SPLIT ∧
        AspisR1CurrentCaller.FirstComposition.firstCurrent
          AdapterRw.solana_program_error.ProgramError.InvalidAccountData vops
          (toDigest (AdapterRw.SolanaDigest.Insts.Aspis_coreDigestDigest32 (install ops vops)))
          (fun error => ops.op44 (fromError error)) f.pub f.proof f.split = ok (.Ok saved) := by
  obtain ⟨native,written⟩ := S2W_D189Wrappers.first_accepted native1 copy std allocator
    e program data initial final saved post accepted
  have owned : AdapterRw.r1_pool_adapter.owned.stage1_owned (install ops vops)
      program e.first data = ok (.Ok saved) :=
    (extraction.stage1 program e.first data).symm.trans native
  have disjoint := first_disjoint e (install ops vops) program data saved owned
  have frame := S2W_AccountObservations.write_frame S2W_ReturnedCheckpoint.encode e.metadata 3 e.heap 2 0 0
    (source (nativeBytes saved)) rfl rfl 1 (fun _ => disjoint 1 (by decide) (by decide))
  have initialObservation := S2W_D189Interpretation.native_observation L sdk S2W_ReturnedCheckpoint.encode e.metadata 3
    world e.heap admission.related admission.entry.valid
  refine ⟨written,?_,?_⟩
  · rw [written]
    exact frame.trans ((congrFun initialObservation 1).symm)
  intro accounts2 f s cuts
  have same := Result.ok.inj (cuts.public1Index.symm.trans (first_index e).2.1)
  have read := cuts.public1Read
  rw [same] at read
  obtain ⟨buffer,size⟩ := AspisS6SdkStage1ReuseFactored.public_read e (install ops vops) f.pub read
  have observed := native_buffer e L sdk world admission.related admission.entry.valid 1
  rw [← buffer] at observed
  exact ⟨buffer,size,observed,AspisS6SdkSourceCutReuse.source_cut_reuse
    ops vops program e.first accounts2 data saved owned f s cuts⟩

#print axioms accepted_sdk_all_cuts
end AspisS6SdkEnclosingCuts
