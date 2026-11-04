import NFR_AfterstateForward16
set_option autoImplicit false
noncomputable section
namespace NFR_AfterstateForward12
open Aeneas Aeneas.Std Result AspisR1TerminalDecoder
open AspisR1.S2K AspisS6NativeAfterstateDecoderFactored NFR_AfterstateForwardHelpers
theorem result (a : Afterstate)
    (valid : pool_v1.pair_terminal.validate_verified_afterstate a = ok (.Ok ())) :
    part_12 (encoded a) a.next_root (a.next_frontier.val[0]'(by have := a.next_frontier.property; scalar_tac)) (a.next_frontier.val[1]'(by have := a.next_frontier.property; scalar_tac)) (a.next_frontier.val[2]'(by have := a.next_frontier.property; scalar_tac)) (a.next_frontier.val[3]'(by have := a.next_frontier.property; scalar_tac)) (a.next_frontier.val[4]'(by have := a.next_frontier.property; scalar_tac)) (a.next_frontier.val[5]'(by have := a.next_frontier.property; scalar_tac)) (a.next_frontier.val[6]'(by have := a.next_frontier.property; scalar_tac)) (a.next_frontier.val[7]'(by have := a.next_frontier.property; scalar_tac)) (a.next_frontier.val[8]'(by have := a.next_frontier.property; scalar_tac)) (a.next_frontier.val[9]'(by have := a.next_frontier.property; scalar_tac)) (a.next_frontier.val[10]'(by have := a.next_frontier.property; scalar_tac)) (a.next_frontier.val[11]'(by have := a.next_frontier.property; scalar_tac)) = ok (.Ok a) := by
  unfold part_12
  rw [range (encoded a) 432#usize 464#usize (DigestBytes.bytes (a.next_frontier.val[12]'(by have := a.next_frontier.property; scalar_tac)))
    (by decide) (by simp [encoded,Array.to_slice,(AfterstateEncoding.bytes a).property])
    (frontier_window a 12 (by decide)),bind_tc_ok]
  rw [AspisR1.JFt_ExactArray.source _ _ _ rfl,bind_tc_ok]
  simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
  rw [NFR_DigestForward.roundtrip _ ((domain a valid).2 ⟨12,by decide⟩),bind_tc_ok]
  simp only [core.result.Result.map_err,core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
  rw [range (encoded a) 464#usize 496#usize (DigestBytes.bytes (a.next_frontier.val[13]'(by have := a.next_frontier.property; scalar_tac)))
    (by decide) (by simp [encoded,Array.to_slice,(AfterstateEncoding.bytes a).property])
    (frontier_window a 13 (by decide)),bind_tc_ok]
  rw [AspisR1.JFt_ExactArray.source _ _ _ rfl,bind_tc_ok]
  simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
  rw [NFR_DigestForward.roundtrip _ ((domain a valid).2 ⟨13,by decide⟩),bind_tc_ok]
  simp only [core.result.Result.map_err,core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
  rw [range (encoded a) 496#usize 528#usize (DigestBytes.bytes (a.next_frontier.val[14]'(by have := a.next_frontier.property; scalar_tac)))
    (by decide) (by simp [encoded,Array.to_slice,(AfterstateEncoding.bytes a).property])
    (frontier_window a 14 (by decide)),bind_tc_ok]
  rw [AspisR1.JFt_ExactArray.source _ _ _ rfl,bind_tc_ok]
  simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
  rw [NFR_DigestForward.roundtrip _ ((domain a valid).2 ⟨14,by decide⟩),bind_tc_ok]
  simp only [core.result.Result.map_err,core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
  rw [range (encoded a) 528#usize 560#usize (DigestBytes.bytes (a.next_frontier.val[15]'(by have := a.next_frontier.property; scalar_tac)))
    (by decide) (by simp [encoded,Array.to_slice,(AfterstateEncoding.bytes a).property])
    (frontier_window a 15 (by decide)),bind_tc_ok]
  rw [AspisR1.JFt_ExactArray.source _ _ _ rfl,bind_tc_ok]
  simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
  rw [NFR_DigestForward.roundtrip _ ((domain a valid).2 ⟨15,by decide⟩),bind_tc_ok]
  simp only [core.result.Result.map_err,core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
  exact NFR_AfterstateForward16.result a valid
#print axioms result
end NFR_AfterstateForward12
