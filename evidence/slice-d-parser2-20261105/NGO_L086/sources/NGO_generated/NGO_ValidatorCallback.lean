import NGO_PrefixLimbsLaw
import NGO_PrefixHighPort
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace NGO_ValidatorCallback
open NGO_PrefixLimbsLaw AspisR1PrefixAggregateParser
noncomputable def invoke (row : U8) (index : Usize) (words : Array U32 8#usize) :
    Result (core.result.Result Unit r1_wire.Error) := do
  let reply ← field.wide_exact.WideExact.from_limbs words
  match reply with
  | none => ok (.Err (.NonCanonical row index))
  | some wide => do
    let high ← field.wide_exact.WideExact.impl.c1 wide
    let bad ← core.cmp.PartialEq.ne.trait_default
      field.QM31.Insts.CoreCmpPartialEqQM31 high field.QM31.ZERO
    if bad then ok (.Err (.NonCanonical row index)) else ok (.Ok ())
/-- Exact full error and source index after the eight canonicality checks and
high-half test, on arbitrary words. The original byte reads/scan still need
composition; this callback fact alone does not close parse_record. -/
theorem result (row : U8) (index : Usize) (words : Array U32 8#usize) :
    invoke row index words=ok (if
      (∀ i : Fin 8, (atWord words i).val<2147483647) ∧
      (atWord words 4).val=0 ∧ (atWord words 5).val=0 ∧
      (atWord words 6).val=0 ∧ (atWord words 7).val=0
      then .Ok () else .Err (.NonCanonical row index)) := by
  unfold invoke
  rw [NGO_PrefixLimbsLaw.result]
  by_cases canonical : ∀ i : Fin 8, (atWord words i).val<2147483647
  · simp only [expected,if_pos canonical,bind_tc_ok,
      field.wide_exact.WideExact.impl.c1]
    rw [NGO_PrefixHighPort.ne]
    by_cases h4 : (atWord words 4).val=0 <;>
      by_cases h5 : (atWord words 5).val=0 <;>
      by_cases h6 : (atWord words 6).val=0 <;>
      by_cases h7 : (atWord words 7).val=0 <;>
      simp [canonical,h4,h5,h6,h7,NGO_PrefixHighPort.nonzero,assembled]
  · simp [expected,canonical]
#print axioms result
end NGO_ValidatorCallback
