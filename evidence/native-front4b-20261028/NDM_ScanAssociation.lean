import NDM_ScanWindow
set_option autoImplicit false
noncomputable section
namespace NDM_ScanAssociation
open Aeneas Aeneas.Std Result
open AspisR1TerminalDecoder pool_v1.pair_terminal

def continueScan (bytes header : Slice U8) : Result (core.result.Result
 AdapterRw.r1_pool_adapter.ScannedAsqaProof AdapterRw.solana_program_error.ProgramError) := do
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

/-- Exact source-model association: SAME original buffer and computed header,
 actual codecs and all their outcomes. No successful decoder result is installed. -/
theorem selected (bytes : Slice U8) (size : bytes.val.length=58295) :
 AspisR1.JHf_Scan.source bytes=continueScan bytes (NDM_ScanWindow.header bytes) := by
 have len : Slice.len bytes=58295#usize := by scalar_tac
 have checked : Usize.checked_add 688#usize 57607#usize=some 58295#usize :=
  AspisR1.AdapterRw.Scalar.checked_add_eq _ _ _ (by scalar_tac)
 unfold AspisR1.JHf_Scan.source
 simp only [lift,checked,bind_tc_ok,len,
  show (58295#usize !=58295#usize)=false from rfl,Bool.false_eq_true,↓reduceIte]
 rw [NDM_ScanWindow.call bytes (by omega)]
 rfl

theorem wrong_length (bytes : Slice U8) (size : bytes.val.length≠58295) :
 AspisR1.JHf_Scan.source bytes=ok (.Err .InvalidAccountData) := by
 have len : Slice.len bytes≠58295#usize := by intro h;apply size;scalar_tac
 have checked : Usize.checked_add 688#usize 57607#usize=some 58295#usize :=
  AspisR1.AdapterRw.Scalar.checked_add_eq _ _ _ (by scalar_tac)
 unfold AspisR1.JHf_Scan.source
 simp [lift,checked,len,size]

theorem proof_tag_shift (bytes : Slice U8) : bytes.val[696]?=(bytes.val.drop 688)[8]? := by
 simp only [List.getElem?_drop]

#print axioms selected
#print axioms wrong_length
#print axioms proof_tag_shift
end NDM_ScanAssociation
