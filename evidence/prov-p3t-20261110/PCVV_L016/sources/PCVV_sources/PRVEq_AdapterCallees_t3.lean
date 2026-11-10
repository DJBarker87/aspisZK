import Aeneas
import AdapterRwModel
import NNH_HostCtx
import NOC_Run5bHost
import AspisR1TerminalDecoder.Funs
import RPz7_S6CurrentAdapterCarrierV1
import PRVEq_AdapterCallees_t2
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
noncomputable section
namespace AdapterRw
namespace PCVV_S3

theorem add_lit (a b c : Std.Usize) (h : a.val + b.val = c.val) : (a + b : Result Std.Usize) = ok c := by
  have hmax : a.val + b.val ≤ Std.Usize.max := by scalar_tac
  obtain ⟨z, hz, hv⟩ := Aeneas.Std.WP.spec_imp_exists (Usize.add_spec (x := a) (y := b) hmax)
  rw [hz]
  congr 1
  apply UScalar.eq_of_val_eq
  omega

abbrev G := AspisR1TerminalDecoder.pool_v1.pair_terminal.decode_pool_v1_pair_verified_afterstate_v1
abbrev Ge := AspisR1TerminalDecoder.pool_v1.pair_terminal.encode_pool_v1_pair_verified_afterstate_v1

theorem slot51 {W Tx : Type} (c : AspisR1.NNH_HostCtx.Ctx W Tx) (x : Ext)
    (kd : AspisR1TerminalDecoder.pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1 →
      aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1)
    (ke : AspisR1TerminalDecoder.pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1 →
      aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1)
    (hP : x.aspis_r1_cost_probe_verifier_PROOF_BYTES = ok 57607#usize)
    (hA : x.aspis_statement_pool_v1_pair_terminal_POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES = ok 688#usize)
    (hT : x.aspis_r1_cost_probe_transport_Variant_tag = fun _ => ok 2#u8)
    (hd : x.aspis_statement_pool_v1_pair_terminal_decode_pool_v1_pair_verified_afterstate_v1 = fun h =>
      do let r ← G h
         ok (match r with
             | core.result.Result.Ok a => core.result.Result.Ok (AspisS6CurrentAdapterCarrier.fromPoolV1PairVerifiedAfterstateV1 a)
             | core.result.Result.Err e => core.result.Result.Err (kd e)))
    (he : x.aspis_statement_pool_v1_pair_terminal_encode_pool_v1_pair_verified_afterstate_v1 = fun a =>
      do let r ← Ge (AspisS6CurrentAdapterCarrier.toPoolV1PairVerifiedAfterstateV1 a)
         ok (match r with
             | core.result.Result.Ok e => core.result.Result.Ok e
             | core.result.Result.Err e => core.result.Result.Err (ke e)))
    (b : Slice Std.U8) :
    (AspisR1.NOC_HostCtx.sdk c).op51 b = r1_pool_adapter.scan_proof_buffer x b := by
  unfold r1_pool_adapter.scan_proof_buffer
  rw [hP, hA, hT, hd, he]
  show (do let expected ← lift (Usize.checked_add 688#usize 57607#usize)
           match expected with
           | none => Result.ok (core.result.Result.Err AdapterRw.solana_program_error.ProgramError.InvalidAccountData)
           | some size =>
             if (b.len != size) = true then
               Result.ok (core.result.Result.Err AdapterRw.solana_program_error.ProgramError.InvalidAccountData)
             else do
               let header ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8) b
                   { start := 0#usize, «end» := 688#usize }
               let decoded ← G header
               match decoded with
               | core.result.Result.Err a =>
                 Result.ok (core.result.Result.Err AdapterRw.solana_program_error.ProgramError.InvalidAccountData)
               | core.result.Result.Ok candidate => do
                 let encoded ← Ge candidate
                 match encoded with
                 | core.result.Result.Err a =>
                   Result.ok (core.result.Result.Err AdapterRw.solana_program_error.ProgramError.InvalidAccountData)
                 | core.result.Result.Ok encoded =>
                   if ((↑encoded : List Std.U8) != (↑header : List Std.U8)) = true then
                     Result.ok (core.result.Result.Err AdapterRw.solana_program_error.ProgramError.InvalidAccountData)
                   else do
                     let tag ← b.index_usize 696#usize
                     if (tag != 2#u8) = true then
                       Result.ok (core.result.Result.Err AdapterRw.solana_program_error.ProgramError.InvalidAccountData)
                     else
                       Result.ok (core.result.Result.Ok
                         ({ candidate_afterstate := AspisS6CurrentAdapterCarrier.fromPoolV1PairVerifiedAfterstateV1 candidate, proof_length := 57607#usize } : r1_pool_adapter.ScannedAsqaProof))) = _
  have h0 : (0#usize + 688#usize : Result Std.Usize) = ok 688#usize := add_lit _ _ _ (by scalar_tac)
  have h8 : (688#usize + 8#usize : Result Std.Usize) = ok 696#usize := add_lit _ _ _ (by scalar_tac)
  simp only [h0, h8, bind_tc_ok]
  cases hco : Usize.checked_add 688#usize 57607#usize with
  | none => rfl
  | some size =>
    have e1 : core.option.Option.ok_or (some size) solana_program_error.ProgramError.InvalidAccountData =
        ok (core.result.Result.Ok size) := rfl
    have e2 : core.result.Result.Insts.CoreOpsTry.branch
        (core.result.Result.Ok size : core.result.Result Std.Usize solana_program_error.ProgramError) =
        ok (core.ops.control_flow.ControlFlow.Continue size) := rfl
    simp only [bind_tc_ok, lift, e1, e2]
    by_cases hl : (b.len != size) = true
    · simp only [hl, if_true]
    · simp only [hl, if_false, Bool.false_eq_true]
      cases hh : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8) b
          { start := 0#usize, «end» := 688#usize } with
      | fail e => rfl
      | div => rfl
      | ok header =>
        simp only [bind_tc_ok]
        cases hg : G header with
        | fail e => rfl
        | div => rfl
        | ok r =>
          cases r with
          | Err e => rfl
          | Ok cand =>
            have m1 : ∀ {A : Type} (v : A), core.result.Result.map_err
                r1_pool_adapter.scan_proof_buffer.closure.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairVerifierTransportErrorV1ProgramError
                (core.result.Result.Ok v : core.result.Result A _) () = ok (core.result.Result.Ok v) := fun _ => rfl
            have m2 : ∀ {A : Type} (v : A), core.result.Result.map_err
                r1_pool_adapter.scan_proof_buffer.closure_1.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairVerifierTransportErrorV1ProgramError
                (core.result.Result.Ok v : core.result.Result A _) () = ok (core.result.Result.Ok v) := fun _ => rfl
            have br : ∀ {A : Type} (v : A), core.result.Result.Insts.CoreOpsTry.branch
                (core.result.Result.Ok v : core.result.Result A solana_program_error.ProgramError) =
                ok (core.ops.control_flow.ControlFlow.Continue v) := fun _ => rfl
            have hne : ∀ (enc : Std.Array Std.U8 688#usize) (hd' : Slice Std.U8),
                (do let s ← Array.Insts.CoreConvertAsRefSlice.as_ref enc
                    core.cmp.impls.PartialEqShared.ne (Slice.Insts.CoreCmpPartialEqSlice core.cmp.PartialEqU8) s hd') =
                ok ((↑enc : List Std.U8) != (↑hd' : List Std.U8)) := by
              intro enc hd'
              rfl
            simp only [bind_tc_ok, m1, m2, br, AspisS6CurrentAdapterCarrier.to_fromPoolV1PairVerifiedAfterstateV1]
            cases hE : Ge cand with
            | fail e => rfl
            | div => rfl
            | ok r =>
              cases r with
              | Err e => rfl
              | Ok enc =>
                simp only [bind_tc_ok, m2, br, hne]
                done
end PCVV_S3
end AdapterRw
