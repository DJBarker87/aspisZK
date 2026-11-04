import NFR_ResultForwardHelpers
set_option autoImplicit false
noncomputable section
namespace NFR_ResultForward
open Aeneas Aeneas.Std Result AspisR1TerminalDecoder
open AspisR1.S2K NFR_ResultForwardHelpers

theorem forward (r : Output)
    (canonical : NBD_DigestInduction.Canonical r.nullifier)
    (afterstate : pool_v1.pair_terminal.validate_verified_afterstate r.verified_afterstate = ok (.Ok ()))
    (validated : pool_v1.pair_forest_terminal.validate_result r = ok (.Ok ())) :
    NFO_RawDecode.decode (encoded r) = ok (.Ok r) := by
  have masterCast := AspisR1.JFt_ExactArray.cast 32#usize r.master_account.to_slice r.master_account rfl
  have selectedCast := AspisR1.JFt_ExactArray.cast 32#usize r.selected_lane_account.to_slice r.selected_lane_account rfl
  have digestCast := AspisR1.JFt_DigestArray.shared (DigestBytes.bytes r.nullifier).to_slice (DigestBytes.bytes r.nullifier) rfl
  have afterstateRoundtrip : pool_v1.pair_terminal.decode_pool_v1_pair_verified_afterstate_v1
      (AfterstateEncoding.bytes r.verified_afterstate).to_slice = ok (.Ok r.verified_afterstate) := by
    simpa only [NFR_AfterstateForwardHelpers.encoded] using
      (NFR_AfterstateForward.roundtrip r.verified_afterstate afterstate)
  unfold NFO_RawDecode.decode
  simp only [show Slice.len (encoded r)=792#usize from by
      unfold encoded; have := (NFO_ResultLayout.bytes r).property; scalar_tac,
    bne_self_eq_false,Bool.false_eq_true,reduceIte,head,
    bind_tc_ok,NFR_AfterstateForward.self_ne,
    get4,get5,get6,get7,
    pool_v1.pair_forest_terminal.POOL_V1_PAIR_FOREST_TERMINAL_VERSION,
    pool_v1.format.POOL_V1_DIGEST_ENCODING_VERSION,kind_roundtrip,
    core.result.Result.Insts.CoreOpsTry.branch,
    pool_v1.pair_forest_terminal.RESULT_MASTER_OFFSET,
    pool_v1.pair_forest_terminal.RESULT_SELECTED_LANE_OFFSET,
    pool_v1.pair_forest_terminal.RESULT_NULLIFIER_OFFSET,
    pool_v1.pair_forest_terminal.RESULT_AFTERSTATE_OFFSET,master_range]
  rw [masterCast,bind_tc_ok]
  rw [NFO_DecodeErrors.master (.Ok r.master_account),bind_tc_ok]
  simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
  rw [selected_range,bind_tc_ok,selectedCast,bind_tc_ok]
  rw [NFO_DecodeErrors.selected (.Ok r.selected_lane_account),bind_tc_ok]
  simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok,get7]
  rw [digest_range,bind_tc_ok,digestCast,bind_tc_ok]
  rw [NFO_DecodeErrors.digest_width (.Ok (DigestBytes.bytes r.nullifier)),bind_tc_ok]
  simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
  rw [NFR_DigestForward.roundtrip _ canonical,bind_tc_ok]
  rw [NFO_DecodeErrors.digest (.Ok r.nullifier),bind_tc_ok]
  simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
  rw [afterstate_range,bind_tc_ok]
  rw [afterstateRoundtrip,bind_tc_ok]
  rw [NFO_DecodeErrors.afterstate (.Ok r.verified_afterstate),bind_tc_ok]
  simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
  have rebuilt : ({transition_kind:=r.transition_kind,master_account:=r.master_account,selected_lane_account:=r.selected_lane_account,output_lane:=r.output_lane,nullifier:=r.nullifier,verified_afterstate:=r.verified_afterstate} : Output) = r := by cases r; rfl
  rw [rebuilt,validated]
  rfl
#print axioms forward

theorem emitted (s : NEU_EmitModel.Statement)
    (valid : pool_v1.pair_forest_terminal.validate_pool_v1_pair_forest_terminal_statement_v1 s = ok (.Ok ())) :
    NFO_PacketDecoder.run (ResultPayload.bytes s).val = ok (.Ok (ResultAdmission.value s)) := by
  have raw := forward (ResultAdmission.value s) (nullifier_domain s valid)
    (StatementAdmission.afterstate s valid) (ResultAdmission.validated s valid)
  rw [NFO_PacketDecoder.on_packet _ (ResultPayload.bytes s).property]
  simpa only [encoded,NFO_ResultLayout.emitted,Array.to_slice] using raw
#print axioms emitted

theorem decoder_association : NFO_PoolReturnData.DecoderAssociation NFO_PacketDecoder.run :=
  emitted
#print axioms decoder_association
end NFR_ResultForward
