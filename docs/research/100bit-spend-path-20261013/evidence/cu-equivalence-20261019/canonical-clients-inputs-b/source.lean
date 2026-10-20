import AspisR1CanonicalDotClients.FunsExternal
import CuSavingsCanonicalDotsSources
set_option autoImplicit false
namespace AspisR1.CuSavingsCanonicalDotClientInputs
open Aeneas Aeneas.Std Result
open AspisR1CanonicalDots
open CuSavingsCanonicalDotsField

/-- Every successful original final-message field read is canonical. The
premise is an execution equation for the exact checked decoder. -/
theorem field_success (bytes : Slice U8) (index : Usize)
    (value : field.wide_exact.WideExact) (h : weights.field bytes index=.ok value) :
    WideCanonical value := by
  unfold weights.field at h
  cases hd : AspisR1CanonicalInputs.weights.field bytes index with
  | fail error => rw [hd] at h; cases h
  | div => rw [hd] at h; cases h
  | ok input =>
    simp only [hd,bind_tc_ok] at h
    cases Result.ok.inj h
    exact CuSavingsCanonicalDotsSources.input_canonical input
      (CuSavingsCanonicalInputParser.field_success bytes index input hd)

/-- Canonicality of a stored partial follows from the actual old finish call,
for every accumulator state, including state reached after any valid prefix. -/
theorem old_finish_success (state : old_pairing.EbyKDot)
    (value : field.wide_exact.WideExact)
    (h : old_pairing.EbyKDot.finish state=.ok value) : WideCanonical value := by
  have he := Result.ok.inj ((CuSavingsCanonicalDotsFinish.old_public_finish state).symm.trans h)
  cases he
  exact CuSavingsCanonicalDotsFinish.result_canonical _ _

theorem new_finish_success (state : new_pairing.EbyKDot)
    (value : field.wide_exact.WideExact)
    (h : new_pairing.EbyKDot.finish state=.ok value) : WideCanonical value := by
  have he := Result.ok.inj ((CuSavingsCanonicalDotsFinish.new_public_finish state).symm.trans h)
  cases he
  exact CuSavingsCanonicalDotsFinish.result_canonical _ _

#print axioms field_success
#print axioms old_finish_success
#print axioms new_finish_success
end AspisR1.CuSavingsCanonicalDotClientInputs
