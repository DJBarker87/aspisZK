import NFR_AfterstateForward12
set_option autoImplicit false
noncomputable section
namespace NFR_AfterstateForward08
open Aeneas Aeneas.Std Result AspisR1TerminalDecoder
open AspisR1.S2K AspisS6NativeAfterstateDecoderFactored NFR_AfterstateForwardHelpers
theorem result (a : Afterstate)
    (valid : pool_v1.pair_terminal.validate_verified_afterstate a = ok (.Ok ())) :
    part_8 (encoded a) a.next_root (a.next_frontier.val[0]'(by have := a.next_frontier.property; scalar_tac)) (a.next_frontier.val[1]'(by have := a.next_frontier.property; scalar_tac)) (a.next_frontier.val[2]'(by have := a.next_frontier.property; scalar_tac)) (a.next_frontier.val[3]'(by have := a.next_frontier.property; scalar_tac)) (a.next_frontier.val[4]'(by have := a.next_frontier.property; scalar_tac)) (a.next_frontier.val[5]'(by have := a.next_frontier.property; scalar_tac)) (a.next_frontier.val[6]'(by have := a.next_frontier.property; scalar_tac)) (a.next_frontier.val[7]'(by have := a.next_frontier.property; scalar_tac)) = ok (.Ok a) := by
  unfold part_8
  rw [range (encoded a) 304#usize 336#usize (DigestBytes.bytes (a.next_frontier.val[8]'(by have := a.next_frontier.property; scalar_tac)))
    (by decide) (by simp [encoded,Array.to_slice,(AfterstateEncoding.bytes a).property])
    (frontier_window a 8 (by decide)),bind_tc_ok]
  rw [AspisR1.JFt_ExactArray.source _ _ _ rfl,bind_tc_ok]
  simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
  rw [NFR_DigestForward.roundtrip _ ((domain a valid).2 ⟨8,by decide⟩),bind_tc_ok]
  simp only [core.result.Result.map_err,core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
  rw [range (encoded a) 336#usize 368#usize (DigestBytes.bytes (a.next_frontier.val[9]'(by have := a.next_frontier.property; scalar_tac)))
    (by decide) (by simp [encoded,Array.to_slice,(AfterstateEncoding.bytes a).property])
    (frontier_window a 9 (by decide)),bind_tc_ok]
  rw [AspisR1.JFt_ExactArray.source _ _ _ rfl,bind_tc_ok]
  simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
  rw [NFR_DigestForward.roundtrip _ ((domain a valid).2 ⟨9,by decide⟩),bind_tc_ok]
  simp only [core.result.Result.map_err,core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
  rw [range (encoded a) 368#usize 400#usize (DigestBytes.bytes (a.next_frontier.val[10]'(by have := a.next_frontier.property; scalar_tac)))
    (by decide) (by simp [encoded,Array.to_slice,(AfterstateEncoding.bytes a).property])
    (frontier_window a 10 (by decide)),bind_tc_ok]
  rw [AspisR1.JFt_ExactArray.source _ _ _ rfl,bind_tc_ok]
  simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
  rw [NFR_DigestForward.roundtrip _ ((domain a valid).2 ⟨10,by decide⟩),bind_tc_ok]
  simp only [core.result.Result.map_err,core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
  rw [range (encoded a) 400#usize 432#usize (DigestBytes.bytes (a.next_frontier.val[11]'(by have := a.next_frontier.property; scalar_tac)))
    (by decide) (by simp [encoded,Array.to_slice,(AfterstateEncoding.bytes a).property])
    (frontier_window a 11 (by decide)),bind_tc_ok]
  rw [AspisR1.JFt_ExactArray.source _ _ _ rfl,bind_tc_ok]
  simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
  rw [NFR_DigestForward.roundtrip _ ((domain a valid).2 ⟨11,by decide⟩),bind_tc_ok]
  simp only [core.result.Result.map_err,core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
  exact NFR_AfterstateForward12.result a valid
#print axioms result
end NFR_AfterstateForward08
