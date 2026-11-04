import NFO_Final
import S6NativeAfterstateCodecV1
import S6NativeDigestAcceptedInverseV1
set_option autoImplicit false
noncomputable section
namespace NFR_RawInverseHelpers
open Aeneas Aeneas.Std Result WP AspisR1TerminalDecoder
open AspisR1.S2K

@[step] theorem afterstate (bytes : Slice U8) :
    pool_v1.pair_terminal.decode_pool_v1_pair_verified_afterstate_v1 bytes
      ⦃ result => ∀ value, result = .Ok value →
        (AfterstateEncoding.bytes value).val = bytes.val ⦄ := by
  obtain ⟨result,run⟩ := AspisS6NativeAfterstateCodec.decode_total bytes
  rw [run,WP.spec_ok]
  intro value accepted
  have frame := AspisS6NativeAfterstateCodec.accepted_frames bytes value
    (run.trans (congrArg ok accepted))
  rw [AspisS6NativeAfterstateEncoderReuse.native_afterstate_contents]
  exact AspisS6NativeAfterstateCodec.decoded_layout bytes value frame
#print axioms afterstate

@[step] theorem digest (bytes : Array U8 32#usize) :
    atomic_statement.decode_digest_canonical bytes
      ⦃ result => ∀ value, result = .Ok value →
        (DigestBytes.bytes value).val = bytes.val ⦄ := by
  obtain ⟨result,run,post⟩ := WP.spec_imp_exists
    (AspisS6NativeDigestAcceptedInverse.decoded_contents bytes)
  rw [run,WP.spec_ok]
  intro value accepted
  rw [AspisS6NativeAfterstateEncoderReuse.native_digest_bytes]
  exact post value accepted
#print axioms digest

@[step] theorem master {T : Type} (r : core.result.Result T core.array.TryFromSliceError) :
    core.result.Result.map_err NFO_RawDecode.decode.closure.Insts.CoreOpsFunctionFnOnceTupleTryFromSliceErrorPoolV1PairForestTerminalFormatErrorV1 r ()
      ⦃ result => ∀ value, result = .Ok value → r = .Ok value ⦄ := by
  apply exists_imp_spec
  cases r <;> refine ⟨_,rfl,?_⟩ <;> simp [core.result.Result.map_err,NFO_RawDecode.decode.closure.Insts.CoreOpsFunctionFnOnceTupleTryFromSliceErrorPoolV1PairForestTerminalFormatErrorV1,NFO_RawDecode.decode.closure.Insts.CoreOpsFunctionFnOnceTupleTryFromSliceErrorPoolV1PairForestTerminalFormatErrorV1.call_once]
#print axioms master

@[step] theorem selected {T : Type} (r : core.result.Result T core.array.TryFromSliceError) :
    core.result.Result.map_err NFO_RawDecode.decode.closure_1.Insts.CoreOpsFunctionFnOnceTupleTryFromSliceErrorPoolV1PairForestTerminalFormatErrorV1 r ()
      ⦃ result => ∀ value, result = .Ok value → r = .Ok value ⦄ := by
  apply exists_imp_spec
  cases r <;> refine ⟨_,rfl,?_⟩ <;> simp [core.result.Result.map_err,NFO_RawDecode.decode.closure_1.Insts.CoreOpsFunctionFnOnceTupleTryFromSliceErrorPoolV1PairForestTerminalFormatErrorV1,NFO_RawDecode.decode.closure_1.Insts.CoreOpsFunctionFnOnceTupleTryFromSliceErrorPoolV1PairForestTerminalFormatErrorV1.call_once]
#print axioms selected

@[step] theorem digest_width {T : Type} (r : core.result.Result T core.array.TryFromSliceError) :
    core.result.Result.map_err NFO_RawDecode.decode.closure_2.Insts.CoreOpsFunctionFnOnceTupleTryFromSliceErrorPoolV1PairForestTerminalFormatErrorV1 r ()
      ⦃ result => ∀ value, result = .Ok value → r = .Ok value ⦄ := by
  apply exists_imp_spec
  cases r <;> refine ⟨_,rfl,?_⟩ <;> simp [core.result.Result.map_err,NFO_RawDecode.decode.closure_2.Insts.CoreOpsFunctionFnOnceTupleTryFromSliceErrorPoolV1PairForestTerminalFormatErrorV1,NFO_RawDecode.decode.closure_2.Insts.CoreOpsFunctionFnOnceTupleTryFromSliceErrorPoolV1PairForestTerminalFormatErrorV1.call_once]
#print axioms digest_width

@[step] theorem digest_error {T : Type} (r : core.result.Result T atomic_statement.AtomicStatementError) :
    core.result.Result.map_err NFO_RawDecode.decode.closure_3.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairForestTerminalFormatErrorV1 r ()
      ⦃ result => ∀ value, result = .Ok value → r = .Ok value ⦄ := by
  apply exists_imp_spec
  cases r <;> refine ⟨_,rfl,?_⟩ <;> simp [core.result.Result.map_err,NFO_RawDecode.decode.closure_3.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairForestTerminalFormatErrorV1,NFO_RawDecode.decode.closure_3.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairForestTerminalFormatErrorV1.call_once]
#print axioms digest_error

@[step] theorem afterstate_error {T : Type} (r : core.result.Result T pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1) :
    core.result.Result.map_err NFO_RawDecode.decode.closure_4.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairVerifierTransportErrorV1PoolV1PairForestTerminalFormatErrorV1 r ()
      ⦃ result => ∀ value, result = .Ok value → r = .Ok value ⦄ := by
  apply exists_imp_spec
  cases r <;> refine ⟨_,rfl,?_⟩ <;> simp [core.result.Result.map_err,NFO_RawDecode.decode.closure_4.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairVerifierTransportErrorV1PoolV1PairForestTerminalFormatErrorV1,NFO_RawDecode.decode.closure_4.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairVerifierTransportErrorV1PoolV1PairForestTerminalFormatErrorV1.call_once]
#print axioms afterstate_error
end NFR_RawInverseHelpers
