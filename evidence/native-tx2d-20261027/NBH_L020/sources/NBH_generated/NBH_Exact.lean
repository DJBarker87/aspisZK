import NBH_ArrayEq
set_option autoImplicit false
namespace NBH_Exact
open Aeneas Aeneas.Std Result AspisR1TerminalDecoder
abbrev Error := pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1

def result (n : Usize) (bytes : Slice U8) : core.result.Result (Array U8 n) Error :=
  if h : bytes.val.length=n.val then .Ok ⟨bytes.val,h⟩ else .Err .WrongLength

theorem source (n : Usize) (bytes : Slice U8) :
    pool_v1.pair_terminal.exact n bytes = ok (result n bytes) := by
  unfold pool_v1.pair_terminal.exact core.array.TryFromArrayCopySlice.try_from
  split <;> simp_all [result,Slice.length,core.result.Result.map_err,
    pool_v1.pair_terminal.exact.closure.Insts.CoreOpsFunctionFnOnceTupleTryFromSliceErrorPoolV1PairVerifierTransportErrorV1,
    pool_v1.pair_terminal.exact.closure.Insts.CoreOpsFunctionFnOnceTupleTryFromSliceErrorPoolV1PairVerifierTransportErrorV1.call_once,
    core.ops.function.FnOnce.call_once, bind_tc_ok]

theorem accepted_bytes (n : Usize) (bytes : Slice U8) (a : Array U8 n)
    (h : pool_v1.pair_terminal.exact n bytes = ok (.Ok a)) : a.val=bytes.val := by
  rw [source] at h
  unfold result at h
  split at h <;> simp_all

theorem rejected (n : Usize) (bytes : Slice U8) :
    pool_v1.pair_terminal.exact n bytes = ok (.Err .WrongLength) ↔ bytes.val.length ≠ n.val := by
  rw [source]
  unfold result
  split <;> simp_all

#print axioms source
#print axioms accepted_bytes
#print axioms rejected
end NBH_Exact
