import Lean
import NGK_NFO_RawDecode

set_option autoImplicit false
namespace NGK_NFO_DecodeErrors
open Aeneas Aeneas.Std Result AspisR1TerminalDecoder
abbrev Error := pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1

theorem digest {T : Type} (r : core.result.Result T atomic_statement.AtomicStatementError) :
    core.result.Result.map_err NGK_NFO_RawDecode.decode.closure_3.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairForestTerminalFormatErrorV1 r () =
    ok (match r with | .Ok v => (.Ok v : core.result.Result T Error) | .Err e => .Err .NonCanonicalDigest) := by
  cases r <;> rfl
#print axioms digest

theorem afterstate {T : Type} (r : core.result.Result T pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1) :
    core.result.Result.map_err NGK_NFO_RawDecode.decode.closure_4.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairVerifierTransportErrorV1PoolV1PairForestTerminalFormatErrorV1 r () =
    ok (match r with | .Ok v => (.Ok v : core.result.Result T Error) | .Err e => .Err (AspisR1TerminalDecoder.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1.Afterstate e)) := by
  cases r <;> rfl
#print axioms afterstate

theorem master {T : Type} (r : core.result.Result T core.array.TryFromSliceError) :
    core.result.Result.map_err NGK_NFO_RawDecode.decode.closure.Insts.CoreOpsFunctionFnOnceTupleTryFromSliceErrorPoolV1PairForestTerminalFormatErrorV1 r () =
    ok (match r with | .Ok v => (.Ok v : core.result.Result T Error) | .Err e => .Err .WrongLength) := by
  cases r <;> rfl
#print axioms master

theorem selected {T : Type} (r : core.result.Result T core.array.TryFromSliceError) :
    core.result.Result.map_err NGK_NFO_RawDecode.decode.closure_1.Insts.CoreOpsFunctionFnOnceTupleTryFromSliceErrorPoolV1PairForestTerminalFormatErrorV1 r () =
    ok (match r with | .Ok v => (.Ok v : core.result.Result T Error) | .Err e => .Err .WrongLength) := by
  cases r <;> rfl
#print axioms selected

theorem digest_width {T : Type} (r : core.result.Result T core.array.TryFromSliceError) :
    core.result.Result.map_err NGK_NFO_RawDecode.decode.closure_2.Insts.CoreOpsFunctionFnOnceTupleTryFromSliceErrorPoolV1PairForestTerminalFormatErrorV1 r () =
    ok (match r with | .Ok v => (.Ok v : core.result.Result T Error) | .Err e => .Err .WrongLength) := by
  cases r <;> rfl
#print axioms digest_width
end NGK_NFO_DecodeErrors

run_cmd do
 let env ← Lean.getEnv
 env.constants.toList.forM fun (n, ci) => do
  if ci.isTheorem && (env.getModuleIdxFor? n).isNone then
   Lean.Elab.Command.elabCommand (← `(command| #print axioms $(Lean.mkIdent n)))
