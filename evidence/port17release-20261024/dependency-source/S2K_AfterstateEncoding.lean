import S2K_AfterstatePrepare

/-! Complete actual extracted ASJA payload from symbolic bounded stores and
ordered little-endian word folds. No independently chosen encoder payload. -/
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1.S2K.AfterstateEncoding
open AspisR1TerminalDecoder pool_v1.pair_terminal
abbrev Afterstate := PoolV1PairVerifiedAfterstateV1

def bytes (a : Afterstate) : Array U8 688#usize :=
  AfterstateBytes.fold a.next_frontier.val 0
    (AfterstatePrepare.value a (Array.repeat 688#usize 0#u8))

theorem encode_exact (a : Afterstate)
    (validated : validate_verified_afterstate a = ok (.Ok ())) :
    encode_pool_v1_pair_verified_afterstate_v1 a = ok (.Ok (bytes a)) := by
  unfold bytes
  simp only [encode_pool_v1_pair_verified_afterstate_v1,validated,
    bind_tc_ok,core.result.Result.Insts.CoreOpsTry.branch]
  generalize Array.repeat 688#usize 0#u8 = output
  change AfterstatePrepare.run a output (fun iter out => do
    let encoded ← encode_pool_v1_pair_verified_afterstate_v1_loop iter out
    ok (core.result.Result.Ok encoded)) = _
  rw [AfterstatePrepare.exact]
  rw [AfterstateBytes.loop_exact a.next_frontier 0#usize (by decide)]
  rfl

#print axioms encode_exact
end AspisR1.S2K.AfterstateEncoding
