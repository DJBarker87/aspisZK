import NEG_RowAssociation
import NEG_RowDomain
set_option autoImplicit false
noncomputable section
namespace NEG_RowStepAssociation
open Aeneas Aeneas.Std Result AspisR1

theorem product_ok (a b : U32) (ha : a.val < 2147483647) (hb : b.val < 2147483647) :
    ∃ p : U64,
      ((core.convert.num.FromU64U32.from a) *
        (core.convert.num.FromU64U32.from b) : Result U64) = ok p ∧
      p.val = a.val*b.val ∧ p.val ≤ 4611686009837453316 := by
  have wa := ExtractedCurrentCM31Mul.widen_value a
  have wb := ExtractedCurrentCM31Mul.widen_value b
  have bound := NEG_RowDomain.product_bound a.val b.val ha hb
  have fit : (core.convert.num.FromU64U32.from a).val *
      (core.convert.num.FromU64U32.from b).val < 2^64 := by rw [wa,wb]; omega
  obtain ⟨p,run,value⟩ := ExtractedCurrentReducerOps.mul_success _ _ fit
  refine ⟨p,run,?_,?_⟩
  · simpa only [wa,wb] using value
  · rw [value,wa,wb];exact bound

/-- The same emitted arithmetic site is an admissible specialization of the
native bounded-product log. This does not assume the desired row output. -/
theorem arithmetic_site (raw : U64) (a b : U32)
    (ha : a.val < 2147483647) (hb : b.val < 2147483647) :
    ∃ p : U64, p.val = a.val*b.val ∧ p.val ≤ 4611686009837453316 ∧
      Port25ARRAY.addWord raw a b = (raw+p : Result U64) := by
  obtain ⟨p,run,value,bound⟩ := product_ok a b ha hb
  refine ⟨p,value,bound,?_⟩
  simp only [Port25ARRAY.addWord,lift,bind_tc_ok,run]

/-- All source iterations establish the exact domains of both CLOSED indexed
read helpers; no caller result, independent successful run, or free word is a
hypothesis. -/
theorem reads (row : Array U64 4#usize) (limbs : Array U32 4#usize)
    (j : Usize) (hj : j.val < 4) :
    ∃ old limb, NEG_RowIsolated.residue_limb_at row j = ok old ∧
      NEG_RowIsolated.power_limb_at limbs j = ok limb ∧
      old = row.val[j.val]'(by rw [row.property];exact hj) ∧
      limb = limbs.val[j.val]'(by rw [limbs.property];exact hj) := by
  obtain ⟨old,hr,hvalue⟩ := WP.spec_imp_exists (Array.index_usize_spec row j hj)
  obtain ⟨limb,hl,lvalue⟩ := WP.spec_imp_exists (Array.index_usize_spec limbs j hj)
  exact ⟨old,limb,hr,hl,hvalue,lvalue⟩

theorem reached_index (iter : core.ops.range.Range Usize)
    (active : iter.start.val < iter.end.val) (stop : iter.end = 4#usize) :
    iter.start.val < 4 := by rw [stop] at active;exact active

#print axioms product_ok
#print axioms arithmetic_site
#print axioms reads
#print axioms reached_index
end NEG_RowStepAssociation
end
