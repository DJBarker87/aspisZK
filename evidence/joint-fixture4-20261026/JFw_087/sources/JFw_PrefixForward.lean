import JFw_Chain
import JFw_RootRead
set_option autoImplicit false
namespace AspisR1.JFw_PrefixForward
open Aeneas Aeneas.Std Result
open AspisR1PrefixAggregateParser ExtractedPrefixTrace
theorem success (bytes : Slice U8) (frames : List (Slice U8)) (finish : Usize)
    (bound : 32 ≤ bytes.length)
    (chain : RecordChain bytes rowOrder 32#usize frames finish)
    (last : finish.val = bytes.length) :
    ∃ pre, r1_wire.Prefix.parse bytes = ok (.Ok pre) := by
  obtain ⟨s,root,read,convert⟩ := JFw_RootRead.read bytes bound
  have enough : ¬Slice.len bytes < 32#usize := by scalar_tac
  have final : finish = Slice.len bytes := UScalar.eq_of_val_eq last
  unfold rowOrder at chain
  cases chain with | cons h0 chain =>
    cases chain with | cons h1 chain =>
      cases chain with | cons h2 chain =>
        cases chain with | cons h3 chain =>
          cases chain with | cons h4 chain =>
            cases chain with | cons h5 chain =>
              cases chain with | cons h6 chain =>
                cases chain with | cons h7 chain =>
                  cases chain with | cons h8 chain =>
                    cases chain with | cons h9 chain =>
                      cases chain with | cons h10 chain =>
                        cases chain with | cons h11 chain =>
                          cases chain with | cons h12 chain =>
                            cases chain with | cons h13 chain =>
                              cases chain with | cons h14 chain =>
                                cases chain with | cons h15 chain =>
                                  cases chain with | cons h16 chain =>
                                    cases chain with | cons h17 chain =>
                                      cases chain with | cons h18 chain =>
                                        cases chain with | cons h19 chain =>
                                          cases chain with | cons h20 chain =>
                                            cases chain with | cons h21 chain =>
                                              cases chain with | cons h22 chain =>
                                                cases chain with | cons h23 chain =>
                                                  cases chain with | cons h24 chain =>
                                                    cases chain with | cons h25 chain =>
                                                      cases chain with | cons h26 chain =>
                                                        cases chain
                                                        refine ⟨?_,?_⟩
                                                        swap
                                                        unfold r1_wire.Prefix.parse
                                                        rw [if_neg enough]
                                                        rw [read]
                                                        conv_lhs => rw [bind_tc_ok]
                                                        with_reducible
                                                          conv_lhs => whnf
                                                        rw [convert]
                                                        conv_lhs => rw [bind_tc_ok]
                                                        with_reducible
                                                          conv_lhs => whnf
                                                        rw [h0]
                                                        conv_lhs => rw [bind_tc_ok]
                                                        conv_lhs => rw [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
                                                        with_reducible
                                                          conv_lhs => whnf
                                                        rw [h1]
                                                        conv_lhs => rw [bind_tc_ok]
                                                        conv_lhs => rw [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
                                                        with_reducible
                                                          conv_lhs => whnf
                                                        rw [h2]
                                                        conv_lhs => rw [bind_tc_ok]
                                                        conv_lhs => rw [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
                                                        with_reducible
                                                          conv_lhs => whnf
                                                        rw [h3]
                                                        conv_lhs => rw [bind_tc_ok]
                                                        conv_lhs => rw [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
                                                        with_reducible
                                                          conv_lhs => whnf
                                                        rw [h4]
                                                        conv_lhs => rw [bind_tc_ok]
                                                        conv_lhs => rw [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
                                                        with_reducible
                                                          conv_lhs => whnf
                                                        rw [h5]
                                                        conv_lhs => rw [bind_tc_ok]
                                                        conv_lhs => rw [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
                                                        with_reducible
                                                          conv_lhs => whnf
                                                        rw [h6]
                                                        conv_lhs => rw [bind_tc_ok]
                                                        conv_lhs => rw [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
                                                        with_reducible
                                                          conv_lhs => whnf
                                                        rw [h7]
                                                        conv_lhs => rw [bind_tc_ok]
                                                        conv_lhs => rw [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
                                                        with_reducible
                                                          conv_lhs => whnf
                                                        rw [h8]
                                                        conv_lhs => rw [bind_tc_ok]
                                                        conv_lhs => rw [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
                                                        with_reducible
                                                          conv_lhs => whnf
                                                        rw [h9]
                                                        conv_lhs => rw [bind_tc_ok]
                                                        conv_lhs => rw [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
                                                        with_reducible
                                                          conv_lhs => whnf
                                                        rw [h10]
                                                        conv_lhs => rw [bind_tc_ok]
                                                        conv_lhs => rw [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
                                                        with_reducible
                                                          conv_lhs => whnf
                                                        rw [h11]
                                                        conv_lhs => rw [bind_tc_ok]
                                                        conv_lhs => rw [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
                                                        with_reducible
                                                          conv_lhs => whnf
                                                        rw [h12]
                                                        conv_lhs => rw [bind_tc_ok]
                                                        conv_lhs => rw [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
                                                        with_reducible
                                                          conv_lhs => whnf
                                                        rw [h13]
                                                        conv_lhs => rw [bind_tc_ok]
                                                        conv_lhs => rw [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
                                                        with_reducible
                                                          conv_lhs => whnf
                                                        rw [h14]
                                                        conv_lhs => rw [bind_tc_ok]
                                                        conv_lhs => rw [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
                                                        with_reducible
                                                          conv_lhs => whnf
                                                        rw [h15]
                                                        conv_lhs => rw [bind_tc_ok]
                                                        conv_lhs => rw [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
                                                        with_reducible
                                                          conv_lhs => whnf
                                                        rw [h16]
                                                        conv_lhs => rw [bind_tc_ok]
                                                        conv_lhs => rw [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
                                                        with_reducible
                                                          conv_lhs => whnf
                                                        rw [h17]
                                                        conv_lhs => rw [bind_tc_ok]
                                                        conv_lhs => rw [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
                                                        with_reducible
                                                          conv_lhs => whnf
                                                        rw [h18]
                                                        conv_lhs => rw [bind_tc_ok]
                                                        conv_lhs => rw [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
                                                        with_reducible
                                                          conv_lhs => whnf
                                                        rw [h19]
                                                        conv_lhs => rw [bind_tc_ok]
                                                        conv_lhs => rw [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
                                                        with_reducible
                                                          conv_lhs => whnf
                                                        rw [h20]
                                                        conv_lhs => rw [bind_tc_ok]
                                                        conv_lhs => rw [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
                                                        with_reducible
                                                          conv_lhs => whnf
                                                        rw [h21]
                                                        conv_lhs => rw [bind_tc_ok]
                                                        conv_lhs => rw [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
                                                        with_reducible
                                                          conv_lhs => whnf
                                                        rw [h22]
                                                        conv_lhs => rw [bind_tc_ok]
                                                        conv_lhs => rw [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
                                                        with_reducible
                                                          conv_lhs => whnf
                                                        rw [h23]
                                                        conv_lhs => rw [bind_tc_ok]
                                                        conv_lhs => rw [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
                                                        with_reducible
                                                          conv_lhs => whnf
                                                        rw [h24]
                                                        conv_lhs => rw [bind_tc_ok]
                                                        conv_lhs => rw [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
                                                        with_reducible
                                                          conv_lhs => whnf
                                                        rw [h25]
                                                        conv_lhs => rw [bind_tc_ok]
                                                        conv_lhs => rw [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
                                                        with_reducible
                                                          conv_lhs => whnf
                                                        rw [h26]
                                                        conv_lhs => rw [bind_tc_ok]
                                                        conv_lhs => rw [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
                                                        with_reducible
                                                          conv_lhs => whnf
                                                        rw [final]
                                                        simp only [bne_self_eq_false,Bool.false_eq_true,if_false]
                                                        rfl
#print axioms success
end AspisR1.JFw_PrefixForward
