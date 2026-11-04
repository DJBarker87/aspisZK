import NFR_AfterstateForward04
set_option autoImplicit false
noncomputable section
namespace NFR_AfterstateForward00
open Aeneas Aeneas.Std Result AspisR1TerminalDecoder
open AspisR1.S2K AspisS6NativeAfterstateDecoderFactored NFR_AfterstateForwardHelpers
theorem result (a : Afterstate)
    (valid : pool_v1.pair_terminal.validate_verified_afterstate a = ok (.Ok ())) :
    part_0 (encoded a) a.next_root  = ok (.Ok a) := by
  unfold part_0
  rw [range (encoded a) 48#usize 80#usize (DigestBytes.bytes (a.next_frontier.val[0]'(by have := a.next_frontier.property; scalar_tac)))
    (by decide) (by simp [encoded,Array.to_slice,(AfterstateEncoding.bytes a).property])
    (frontier_window a 0 (by decide)),bind_tc_ok]
  rw [AspisR1.JFt_ExactArray.source _ _ _ rfl,bind_tc_ok]
  simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
  rw [NFR_DigestForward.roundtrip _ ((domain a valid).2 ⟨0,by decide⟩),bind_tc_ok]
  simp only [core.result.Result.map_err,core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
  rw [range (encoded a) 80#usize 112#usize (DigestBytes.bytes (a.next_frontier.val[1]'(by have := a.next_frontier.property; scalar_tac)))
    (by decide) (by simp [encoded,Array.to_slice,(AfterstateEncoding.bytes a).property])
    (frontier_window a 1 (by decide)),bind_tc_ok]
  rw [AspisR1.JFt_ExactArray.source _ _ _ rfl,bind_tc_ok]
  simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
  rw [NFR_DigestForward.roundtrip _ ((domain a valid).2 ⟨1,by decide⟩),bind_tc_ok]
  simp only [core.result.Result.map_err,core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
  rw [range (encoded a) 112#usize 144#usize (DigestBytes.bytes (a.next_frontier.val[2]'(by have := a.next_frontier.property; scalar_tac)))
    (by decide) (by simp [encoded,Array.to_slice,(AfterstateEncoding.bytes a).property])
    (frontier_window a 2 (by decide)),bind_tc_ok]
  rw [AspisR1.JFt_ExactArray.source _ _ _ rfl,bind_tc_ok]
  simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
  rw [NFR_DigestForward.roundtrip _ ((domain a valid).2 ⟨2,by decide⟩),bind_tc_ok]
  simp only [core.result.Result.map_err,core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
  rw [range (encoded a) 144#usize 176#usize (DigestBytes.bytes (a.next_frontier.val[3]'(by have := a.next_frontier.property; scalar_tac)))
    (by decide) (by simp [encoded,Array.to_slice,(AfterstateEncoding.bytes a).property])
    (frontier_window a 3 (by decide)),bind_tc_ok]
  rw [AspisR1.JFt_ExactArray.source _ _ _ rfl,bind_tc_ok]
  simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
  rw [NFR_DigestForward.roundtrip _ ((domain a valid).2 ⟨3,by decide⟩),bind_tc_ok]
  simp only [core.result.Result.map_err,core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
  exact NFR_AfterstateForward04.result a valid
#print axioms result
end NFR_AfterstateForward00
