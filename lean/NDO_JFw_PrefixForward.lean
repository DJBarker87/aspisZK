import JFw_Chain
import NDO_JFw_RootRead
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
                                                        change (do let r ← r1_wire.parse_record_at bytes 0#u8 _; _) = _
                                                        rw [h0]
                                                        conv_lhs => rw [bind_tc_ok]
                                                        conv_lhs => rw [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
                                                        with_reducible
                                                          conv_lhs => whnf
                                                        change (do let r ← r1_wire.parse_record_at bytes 1#u8 _; _) = _
                                                        rw [h1]
                                                        conv_lhs => rw [bind_tc_ok]
                                                        conv_lhs => rw [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
                                                        with_reducible
                                                          conv_lhs => whnf
                                                        change (do let r ← r1_wire.parse_record_at bytes 2#u8 _; _) = _
                                                        rw [h2]
                                                        conv_lhs => rw [bind_tc_ok]
                                                        conv_lhs => rw [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
                                                        with_reducible
                                                          conv_lhs => whnf
                                                        change (do let r ← r1_wire.parse_record_at bytes 3#u8 _; _) = _
                                                        rw [h3]
                                                        conv_lhs => rw [bind_tc_ok]
                                                        conv_lhs => rw [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
                                                        with_reducible
                                                          conv_lhs => whnf
                                                        change (do let r ← r1_wire.parse_record_at bytes 4#u8 _; _) = _
                                                        rw [h4]
                                                        conv_lhs => rw [bind_tc_ok]
                                                        conv_lhs => rw [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
                                                        with_reducible
                                                          conv_lhs => whnf
                                                        change (do let r ← r1_wire.parse_record_at bytes 5#u8 _; _) = _
                                                        rw [h5]
                                                        conv_lhs => rw [bind_tc_ok]
                                                        conv_lhs => rw [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
                                                        with_reducible
                                                          conv_lhs => whnf
                                                        change (do let r ← r1_wire.parse_record_at bytes 6#u8 _; _) = _
                                                        rw [h6]
                                                        conv_lhs => rw [bind_tc_ok]
                                                        conv_lhs => rw [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
                                                        with_reducible
                                                          conv_lhs => whnf
                                                        change (do let r ← r1_wire.parse_record_at bytes 7#u8 _; _) = _
                                                        rw [h7]
                                                        conv_lhs => rw [bind_tc_ok]
                                                        conv_lhs => rw [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
                                                        with_reducible
                                                          conv_lhs => whnf
                                                        change (do let r ← r1_wire.parse_record_at bytes 8#u8 _; _) = _
                                                        rw [h8]
                                                        conv_lhs => rw [bind_tc_ok]
                                                        conv_lhs => rw [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
                                                        with_reducible
                                                          conv_lhs => whnf
                                                        change (do let r ← r1_wire.parse_record_at bytes 9#u8 _; _) = _
                                                        rw [h9]
                                                        conv_lhs => rw [bind_tc_ok]
                                                        conv_lhs => rw [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
                                                        with_reducible
                                                          conv_lhs => whnf
                                                        change (do let r ← r1_wire.parse_record_at bytes 10#u8 _; _) = _
                                                        rw [h10]
                                                        conv_lhs => rw [bind_tc_ok]
                                                        conv_lhs => rw [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
                                                        with_reducible
                                                          conv_lhs => whnf
                                                        change (do let r ← r1_wire.parse_record_at bytes 11#u8 _; _) = _
                                                        rw [h11]
                                                        conv_lhs => rw [bind_tc_ok]
                                                        conv_lhs => rw [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
                                                        with_reducible
                                                          conv_lhs => whnf
                                                        change (do let r ← r1_wire.parse_record_at bytes 12#u8 _; _) = _
                                                        rw [h12]
                                                        conv_lhs => rw [bind_tc_ok]
                                                        conv_lhs => rw [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
                                                        with_reducible
                                                          conv_lhs => whnf
                                                        change (do let r ← r1_wire.parse_record_at bytes 13#u8 _; _) = _
                                                        rw [h13]
                                                        conv_lhs => rw [bind_tc_ok]
                                                        conv_lhs => rw [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
                                                        with_reducible
                                                          conv_lhs => whnf
                                                        change (do let r ← r1_wire.parse_record_at bytes 14#u8 _; _) = _
                                                        rw [h14]
                                                        conv_lhs => rw [bind_tc_ok]
                                                        conv_lhs => rw [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
                                                        with_reducible
                                                          conv_lhs => whnf
                                                        change (do let r ← r1_wire.parse_record_at bytes 15#u8 _; _) = _
                                                        rw [h15]
                                                        conv_lhs => rw [bind_tc_ok]
                                                        conv_lhs => rw [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
                                                        with_reducible
                                                          conv_lhs => whnf
                                                        change (do let r ← r1_wire.parse_record_at bytes 16#u8 _; _) = _
                                                        rw [h16]
                                                        conv_lhs => rw [bind_tc_ok]
                                                        conv_lhs => rw [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
                                                        with_reducible
                                                          conv_lhs => whnf
                                                        change (do let r ← r1_wire.parse_record_at bytes 17#u8 _; _) = _
                                                        rw [h17]
                                                        conv_lhs => rw [bind_tc_ok]
                                                        conv_lhs => rw [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
                                                        with_reducible
                                                          conv_lhs => whnf
                                                        change (do let r ← r1_wire.parse_record_at bytes 18#u8 _; _) = _
                                                        rw [h18]
                                                        conv_lhs => rw [bind_tc_ok]
                                                        conv_lhs => rw [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
                                                        with_reducible
                                                          conv_lhs => whnf
                                                        change (do let r ← r1_wire.parse_record_at bytes 19#u8 _; _) = _
                                                        rw [h19]
                                                        conv_lhs => rw [bind_tc_ok]
                                                        conv_lhs => rw [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
                                                        with_reducible
                                                          conv_lhs => whnf
                                                        change (do let r ← r1_wire.parse_record_at bytes 20#u8 _; _) = _
                                                        rw [h20]
                                                        conv_lhs => rw [bind_tc_ok]
                                                        conv_lhs => rw [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
                                                        with_reducible
                                                          conv_lhs => whnf
                                                        change (do let r ← r1_wire.parse_record_at bytes 21#u8 _; _) = _
                                                        rw [h21]
                                                        conv_lhs => rw [bind_tc_ok]
                                                        conv_lhs => rw [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
                                                        with_reducible
                                                          conv_lhs => whnf
                                                        change (do let r ← r1_wire.parse_record_at bytes 22#u8 _; _) = _
                                                        rw [h22]
                                                        conv_lhs => rw [bind_tc_ok]
                                                        conv_lhs => rw [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
                                                        with_reducible
                                                          conv_lhs => whnf
                                                        change (do let r ← r1_wire.parse_record_at bytes 23#u8 _; _) = _
                                                        rw [h23]
                                                        conv_lhs => rw [bind_tc_ok]
                                                        conv_lhs => rw [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
                                                        with_reducible
                                                          conv_lhs => whnf
                                                        change (do let r ← r1_wire.parse_record_at bytes 24#u8 _; _) = _
                                                        rw [h24]
                                                        conv_lhs => rw [bind_tc_ok]
                                                        conv_lhs => rw [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
                                                        with_reducible
                                                          conv_lhs => whnf
                                                        change (do let r ← r1_wire.parse_record_at bytes 25#u8 _; _) = _
                                                        rw [h25]
                                                        conv_lhs => rw [bind_tc_ok]
                                                        conv_lhs => rw [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
                                                        with_reducible
                                                          conv_lhs => whnf
                                                        change (do let r ← r1_wire.parse_record_at bytes 26#u8 _; _) = _
                                                        rw [h26]
                                                        conv_lhs => rw [bind_tc_ok]
                                                        conv_lhs => rw [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
                                                        with_reducible
                                                          conv_lhs => whnf
                                                        rw [final]
                                                        change (if Slice.len bytes != Slice.len bytes then _ else _) = _
                                                        simp only [bne_self_eq_false,Bool.false_eq_true,if_false]
                                                        rfl
#print axioms success
end AspisR1.JFw_PrefixForward
