import S6SdkSelectedSemanticCutV1
import S6SdkOriginalObjectCallerV1
import S6SdkStage1ReuseFactoredV1
import S6SdkSourceCutReuseV1
set_option autoImplicit false
noncomputable section
namespace AspisS6SdkSelectedSemanticCaller
open Aeneas Aeneas.Std Result
open AspisR1 S2Trust S2W_D189Entry S2W_D189Wrappers S2W_TrustedStd
open S2W_WrapperLaws S2W_ReturnedCheckpoint S2W_EntryWriteHistory S2W_CommittedCheckpoint
open S2W_NativeConsolidation AspisS6CurrentFirstInstallation AspisS6CurrentVerifierCarrier
open AspisS6CurrentCodecInstallation AspisS6CurrentAdapterCarrier
/-- From ONE original SDK acceptance, choose the ACTUAL selected semantic
argument for each existing matching cut, preserving every other full cut field
and the same second cut. Public bytes/codec/checkpoint frame and first reuse are
retained. This does not assert arbitrary original f.semantic identity. -/
theorem original_sdk_selected_cuts {W A : Type}
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
    (accepted : AspisS6SdkFirstObjectEquivalence.originalFirst native1 copy allocator e program data initial =
      ok (.Ok (saved,post,final))) :
    post = writeBracket e.heap 2 0 0 (source (nativeBytes saved)) ∧
    S2W_AccountObservations.observe S2W_ReturnedCheckpoint.encode e.metadata 3 post 1 =
      S2W_D189Interpretation.nativeObserve L S2W_ReturnedCheckpoint.encode e.metadata 3 world e.heap.ambient 1 ∧
    ∀ (accounts2 : Slice AdapterRw.Cuts.Account) (f : FirstCut) (s : SecondCut),
      SourceCuts (install ops vops) e.first accounts2 saved f s →
      ∃ semantic,
        AdapterRw.aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1.semantic_public
          f.statement = ok semantic ∧
        SourceCuts (install ops vops) e.first accounts2 saved {f with semantic := semantic} s ∧
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
  have wrapped : S2W_D189Wrappers.first native1 copy allocator e program data initial =
      ok (.Ok (saved,post,final)) := by
    rw [AspisS6SdkFirstObjectEquivalence.first_eq_original]
    exact accepted
  obtain ⟨written,frame,allCuts⟩ := AspisS6SdkEnclosingCuts.accepted_sdk_all_cuts
    L sdk copy std allocator e world admission ops vops native1 native2 hashv extraction
    program data initial final saved post wrapped
  obtain ⟨native,_⟩ := S2W_D189Wrappers.first_accepted native1 copy std allocator
    e program data initial final saved post wrapped
  have owned : AdapterRw.r1_pool_adapter.owned.stage1_owned (install ops vops)
      program e.first data = ok (.Ok saved) :=
    (extraction.stage1 program e.first data).symm.trans native
  refine ⟨written,frame,?_⟩
  intro accounts2 f s cuts
  obtain ⟨semantic,selected,chosen,_⟩ := AspisS6SdkSelectedSemanticCut.selected_cut
    ops vops program e.first accounts2 data saved owned f s cuts
  exact ⟨semantic,selected,chosen,allCuts accounts2 f s cuts⟩

#print axioms original_sdk_selected_cuts
end AspisS6SdkSelectedSemanticCaller
end
