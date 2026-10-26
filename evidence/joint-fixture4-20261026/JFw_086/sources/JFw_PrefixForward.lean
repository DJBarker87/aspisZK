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
                                                        with_reducible
                                                          conv_lhs => whnf
                                                        rw [convert]
                                                        with_reducible
                                                          conv_lhs => whnf
                                                        rw [h0]
                                                        with_reducible
                                                          conv_lhs => whnf
                                                        rw [h1]
                                                        with_reducible
                                                          conv_lhs => whnf
                                                        rw [h2]
                                                        with_reducible
                                                          conv_lhs => whnf
                                                        rw [h3]
                                                        with_reducible
                                                          conv_lhs => whnf
                                                        rw [h4]
                                                        with_reducible
                                                          conv_lhs => whnf
                                                        rw [h5]
                                                        with_reducible
                                                          conv_lhs => whnf
                                                        rw [h6]
                                                        with_reducible
                                                          conv_lhs => whnf
                                                        rw [h7]
                                                        with_reducible
                                                          conv_lhs => whnf
                                                        rw [h8]
                                                        with_reducible
                                                          conv_lhs => whnf
                                                        rw [h9]
                                                        with_reducible
                                                          conv_lhs => whnf
                                                        rw [h10]
                                                        with_reducible
                                                          conv_lhs => whnf
                                                        rw [h11]
                                                        with_reducible
                                                          conv_lhs => whnf
                                                        rw [h12]
                                                        with_reducible
                                                          conv_lhs => whnf
                                                        rw [h13]
                                                        with_reducible
                                                          conv_lhs => whnf
                                                        rw [h14]
                                                        with_reducible
                                                          conv_lhs => whnf
                                                        rw [h15]
                                                        with_reducible
                                                          conv_lhs => whnf
                                                        rw [h16]
                                                        with_reducible
                                                          conv_lhs => whnf
                                                        rw [h17]
                                                        with_reducible
                                                          conv_lhs => whnf
                                                        rw [h18]
                                                        with_reducible
                                                          conv_lhs => whnf
                                                        rw [h19]
                                                        with_reducible
                                                          conv_lhs => whnf
                                                        rw [h20]
                                                        with_reducible
                                                          conv_lhs => whnf
                                                        rw [h21]
                                                        with_reducible
                                                          conv_lhs => whnf
                                                        rw [h22]
                                                        with_reducible
                                                          conv_lhs => whnf
                                                        rw [h23]
                                                        with_reducible
                                                          conv_lhs => whnf
                                                        rw [h24]
                                                        with_reducible
                                                          conv_lhs => whnf
                                                        rw [h25]
                                                        with_reducible
                                                          conv_lhs => whnf
                                                        rw [h26]
                                                        with_reducible
                                                          conv_lhs => whnf
                                                        rw [final]
                                                        simp only [bne_self_eq_false,Bool.false_eq_true,if_false]
                                                        rfl
#print axioms success
end AspisR1.JFw_PrefixForward
