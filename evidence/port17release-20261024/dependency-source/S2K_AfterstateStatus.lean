import S2K_AfterstatePrefix

/-! Exact status composition of the actual extracted encoder, retaining every
validator error. No successful encoder premise or external certificate axiom. -/
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1.S2K.AfterstateStatus
open AspisR1TerminalDecoder
open pool_v1.pair_terminal
abbrev Afterstate := PoolV1PairVerifiedAfterstateV1
abbrev Error := PoolV1PairVerifierTransportErrorV1

def finish (p : LoopStep.Iter × Array U8 688#usize) :
    Result (core.result.Result (Array U8 688#usize) Error) := do
  let out ← encode_pool_v1_pair_verified_afterstate_v1_loop p.1 p.2
  ok (.Ok out)

private theorem finish_total (rows : AfterstateLoop.Rows) (out : Array U8 688#usize) :
    ∃ bytes, (do
      let result ← encode_pool_v1_pair_verified_afterstate_v1_loop (Iterator.cursor rows 0#usize) out
      ok (core.result.Result.Ok result : core.result.Result (Array U8 688#usize) Error)) = ok (.Ok bytes) := by
  obtain ⟨bytes,run⟩ := AfterstateLoop.total rows out
  exact ⟨bytes, by rw [run]; rfl⟩

theorem success (a : Afterstate)
    (validated : validate_verified_afterstate a = ok (.Ok ())) :
    ∃ bytes, encode_pool_v1_pair_verified_afterstate_v1 a = ok (.Ok bytes) := by
  obtain ⟨root,encoded⟩ := DigestTotal.total a.next_root
  simp only [encode_pool_v1_pair_verified_afterstate_v1,validated,
    bind_tc_ok,core.result.Result.Insts.CoreOpsTry.branch]
  generalize Array.repeat 688#usize 0#u8 = output
  simp only [encoded,bind_tc_ok,lift]
  simp [core.array.Array.index_mut, core.ops.index.IndexMutSlice,
    core.slice.index.Slice.index_mut, core.slice.index.SliceIndexRangeToUsizeSlice,
    core.slice.index.SliceIndexRangeToUsizeSlice.index_mut,
    core.slice.index.SliceIndexRangeUsizeSlice,
    core.slice.index.SliceIndexRangeUsizeSlice.index_mut,
    Array.to_slice, Array.from_slice, core.slice.Slice.copy_from_slice,
    Slice.length, Slice.len, Array.update, output.property, List.slice,
    pool_v1.pair_terminal.POOL_V1_PAIR_VERIFIED_AFTERSTATE_MAGIC,
    core.slice.Slice.iter, core.iter.traits.iterator.Iterator.enumerate.trait_default,
    core.iter.traits.iterator.Iterator.enumerate.default, Iterator.cursor]

  exact finish_total a.next_frontier _

theorem rejection (a : Afterstate) (e : Error)
    (validated : validate_verified_afterstate a = ok (.Err e)) :
    encode_pool_v1_pair_verified_afterstate_v1 a = ok (.Err e) := by
  simp only [encode_pool_v1_pair_verified_afterstate_v1, validated,
    bind_tc_ok, core.result.Result.Insts.CoreOpsTry.branch]
  rfl


def status (r : Result (core.result.Result (Array U8 688#usize) Error)) :
    Result (core.result.Result Unit Error) := do
  let reply ← r
  match reply with
  | .Ok _ => ok (.Ok ())
  | .Err e => ok (.Err e)

theorem status_exact (a : Afterstate) :
    status (encode_pool_v1_pair_verified_afterstate_v1 a) = validate_verified_afterstate a := by
  cases validated : validate_verified_afterstate a with
  | fail e => simp only [encode_pool_v1_pair_verified_afterstate_v1, validated, bind_tc_fail, status]
  | div => simp only [encode_pool_v1_pair_verified_afterstate_v1, validated, bind_tc_div, status]
  | ok reply =>
    cases reply with
    | Err e => rw [rejection a e validated]; rfl
    | Ok unit =>
      cases unit
      obtain ⟨bytes,run⟩ := success a validated
      rw [run]
      rfl

#print axioms finish_total
#print axioms success
#print axioms rejection
#print axioms status_exact
end AspisR1.S2K.AfterstateStatus
