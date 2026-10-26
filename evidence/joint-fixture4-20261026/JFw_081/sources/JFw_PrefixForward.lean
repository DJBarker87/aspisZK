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
                                                        unfold r1_wire.Prefix.parse
                                                        simp only [if_neg enough,read,convert,bind_tc_ok,core.result.Result.Insts.CoreOpsTry.branch,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,h13,h14,h15,h16,h17,h18,h19,h20,h21,h22,h23,h24,h25,h26,final,bne_self_eq_false,Bool.false_eq_true,if_false]
                                                        exact ⟨_,rfl⟩
#print axioms success
end AspisR1.JFw_PrefixForward
