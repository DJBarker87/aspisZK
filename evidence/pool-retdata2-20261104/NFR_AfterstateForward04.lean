import NFR_AfterstateForward08
set_option autoImplicit false
noncomputable section
namespace NFR_AfterstateForward04
open Aeneas Aeneas.Std Result AspisR1TerminalDecoder
open AspisR1.S2K AspisS6NativeAfterstateDecoderFactored NFR_AfterstateForwardHelpers
theorem result (a : Afterstate)
    (valid : pool_v1.pair_terminal.validate_verified_afterstate a = ok (.Ok ())) :
    part_4 (encoded a) a.next_root (a.next_frontier.val[0]'(by have := a.next_frontier.property; scalar_tac)) (a.next_frontier.val[1]'(by have := a.next_frontier.property; scalar_tac)) (a.next_frontier.val[2]'(by have := a.next_frontier.property; scalar_tac)) (a.next_frontier.val[3]'(by have := a.next_frontier.property; scalar_tac)) = ok (.Ok a) := by
  unfold part_4
  rw [range (encoded a) 176#usize 208#usize (DigestBytes.bytes (a.next_frontier.val[4]'(by have := a.next_frontier.property; scalar_tac)))
    (by decide) (by simp [encoded,Array.to_slice,(AfterstateEncoding.bytes a).property])
    (frontier_window a 4 (by decide)),bind_tc_ok]
  rw [AspisR1.JFt_ExactArray.source _ _ _ rfl,bind_tc_ok]
  simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
  rw [NFR_DigestForward.roundtrip _ ((domain a valid).2 ⟨4,by decide⟩),bind_tc_ok]
  simp only [core.result.Result.map_err,core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
  rw [range (encoded a) 208#usize 240#usize (DigestBytes.bytes (a.next_frontier.val[5]'(by have := a.next_frontier.property; scalar_tac)))
    (by decide) (by simp [encoded,Array.to_slice,(AfterstateEncoding.bytes a).property])
    (frontier_window a 5 (by decide)),bind_tc_ok]
  rw [AspisR1.JFt_ExactArray.source _ _ _ rfl,bind_tc_ok]
  simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
  rw [NFR_DigestForward.roundtrip _ ((domain a valid).2 ⟨5,by decide⟩),bind_tc_ok]
  simp only [core.result.Result.map_err,core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
  rw [range (encoded a) 240#usize 272#usize (DigestBytes.bytes (a.next_frontier.val[6]'(by have := a.next_frontier.property; scalar_tac)))
    (by decide) (by simp [encoded,Array.to_slice,(AfterstateEncoding.bytes a).property])
    (frontier_window a 6 (by decide)),bind_tc_ok]
  rw [AspisR1.JFt_ExactArray.source _ _ _ rfl,bind_tc_ok]
  simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
  rw [NFR_DigestForward.roundtrip _ ((domain a valid).2 ⟨6,by decide⟩),bind_tc_ok]
  simp only [core.result.Result.map_err,core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
  rw [range (encoded a) 272#usize 304#usize (DigestBytes.bytes (a.next_frontier.val[7]'(by have := a.next_frontier.property; scalar_tac)))
    (by decide) (by simp [encoded,Array.to_slice,(AfterstateEncoding.bytes a).property])
    (frontier_window a 7 (by decide)),bind_tc_ok]
  rw [AspisR1.JFt_ExactArray.source _ _ _ rfl,bind_tc_ok]
  simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
  rw [NFR_DigestForward.roundtrip _ ((domain a valid).2 ⟨7,by decide⟩),bind_tc_ok]
  simp only [core.result.Result.map_err,core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
  exact NFR_AfterstateForward08.result a valid
#print axioms result
end NFR_AfterstateForward04
