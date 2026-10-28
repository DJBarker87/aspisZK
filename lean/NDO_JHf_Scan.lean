import AdapterRwScalar
import NDO_JHf_ProofWindow
import NDO_JHf_ScanCodec
import NDO_JHd_ScanValue
import RPz7_S6CurrentAdapterCarrierV1
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHf_Scan
open Aeneas Aeneas.Std Result
open AspisR1TerminalDecoder pool_v1.pair_terminal

/-- Direct source control-flow model of scan_proof_buffer. Both codecs are
actual extracted operations; no successful child return is installed.
Native/source/ELF association of this model remains a separate obligation. -/
def source (bytes : Slice U8) : Result (core.result.Result
    AdapterRw.r1_pool_adapter.ScannedAsqaProof AdapterRw.solana_program_error.ProgramError) := do
  let expected ← lift (Usize.checked_add 688#usize 57607#usize)
  match expected with
  | none=>ok (.Err .InvalidAccountData)
  | some size=>
    if Slice.len bytes != size then ok (.Err .InvalidAccountData) else do
      let header ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
        bytes {start:=0#usize,«end»:=688#usize}
      let decoded ← decode_pool_v1_pair_verified_afterstate_v1 header
      match decoded with
      | .Err _=>ok (.Err .InvalidAccountData)
      | .Ok candidate=>
        let encoded ← encode_pool_v1_pair_verified_afterstate_v1 candidate
        match encoded with
        | .Err _=>ok (.Err .InvalidAccountData)
        | .Ok encoded=>
          if encoded.val != header.val then ok (.Err .InvalidAccountData) else do
            let tag ← Slice.index_usize bytes 696#usize
            if tag != 2#u8 then ok (.Err .InvalidAccountData) else
              ok (.Ok ⟨AspisS6CurrentAdapterCarrier.fromPoolV1PairVerifiedAfterstateV1 candidate,57607#usize⟩)

attribute [local irreducible] JHb_Header.account JHb_Header.value

theorem real : source JHb_Header.account=ok (.Ok JHd_ScanValue.value) := by
  have size : Slice.len JHb_Header.account=58295#usize := by
    have h:=JHb_Header.length
    scalar_tac
  unfold source
  simp only [lift,show Usize.checked_add 688#usize 57607#usize=some 58295#usize from AdapterRw.Scalar.checked_add_eq _ _ _ (by scalar_tac),
    bind_tc_ok,size,show (58295#usize !=58295#usize)=false from rfl,Bool.false_eq_true,↓reduceIte,
    JHf_ProofWindow.first,JHb_Header.candidate,JHf_ScanCodec.encoded,
    show (JHb_Header.value.val !=JHb_Header.value.to_slice.val)=false from by simp only [Array.to_slice];simp,
    JHf_ProofWindow.tag,show (2#u8 !=2#u8)=false from rfl]
  rfl
#print axioms real
end AspisR1.JHf_Scan
end
