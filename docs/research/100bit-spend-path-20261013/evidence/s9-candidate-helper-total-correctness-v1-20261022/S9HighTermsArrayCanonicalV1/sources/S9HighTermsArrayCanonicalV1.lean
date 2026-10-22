import S9HighTermsTraceV1

set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1S9HighTermsArrayCanonicalV1

private theorem usize_eq_of_val_eq (a b : Std.Usize) (h : a.val = b.val) : a = b := by
  cases a with
  | mk av =>
    cases b with
    | mk bv =>
      simp only [UScalar.val] at h
      have hab := BitVec.eq_of_toNat_eq h
      subst bv
      rfl

private theorem index_success_bound {A : Type} {N : Std.Usize}
    (a : Array A N) (i : Std.Usize) (x : A)
    (h : Array.index_usize a i = .ok x) : i.val < N.val := by
  unfold Array.index_usize at h
  cases hopt : a[i]? with
  | none => simp [hopt] at h
  | some y =>
      have hsome : a.val[i.val]? = some y := by simpa using hopt
      have hlen : i.val < a.val.length := (List.getElem?_eq_some_iff.mp hsome).1
      simpa only [a.property] using hlen

/-- Every indexed read from the exact terms array returned by a four-call
trace is canonical, by its recorded list of those same four callback outputs. -/
theorem high_terms_returned_array_reads_canonical
    (ap1 : Array AspisR1S9HighTermsTraceV1.W (4#usize))
    (high : Array AspisR1S9HighTermsTraceV1.Q (4#usize))
    (hterms : AspisR1S9HighTermsTraceV1.HighTermsFour ap1 high) :
    ∀ (j : Std.Usize) (x : AspisR1S9HighTermsTraceV1.W),
      Array.index_usize hterms.terms j = .ok x →
      AspisR1S9HighTermsTraceV1.canonicalW x := by
  intro j x hread
  have hjbound := index_success_bound hterms.terms j x hread
  have hjcases : j.val = 0 ∨ j.val = 1 ∨ j.val = 2 ∨ j.val = 3 := by
    have hfour : (4#usize).val = 4 := by decide
    have hjlt : j.val < 4 := by simpa only [hfour] using hjbound
    omega
  rcases hjcases with hj | hj | hj | hj
  · have heq : j = 0#usize := usize_eq_of_val_eq j 0#usize (by simpa using hj)
    subst j
    have hslot : Array.index_usize hterms.terms 0#usize = .ok hterms.call0.term := by
      unfold Array.index_usize
      simp only [Array.getElem?_Usize_eq]
      simp only [hterms.terms_values]
      simp
    have hx : x = hterms.call0.term := Result.ok.inj (hread.symm.trans hslot)
    simpa [hx] using hterms.call0.term_canonical
  · have heq : j = 1#usize := usize_eq_of_val_eq j 1#usize (by simpa using hj)
    subst j
    have hslot : Array.index_usize hterms.terms 1#usize = .ok hterms.call1.term := by
      unfold Array.index_usize
      simp only [Array.getElem?_Usize_eq]
      simp only [hterms.terms_values]
      simp
    have hx : x = hterms.call1.term := Result.ok.inj (hread.symm.trans hslot)
    simpa [hx] using hterms.call1.term_canonical
  · have heq : j = 2#usize := usize_eq_of_val_eq j 2#usize (by simpa using hj)
    subst j
    have hslot : Array.index_usize hterms.terms 2#usize = .ok hterms.call2.term := by
      unfold Array.index_usize
      simp only [Array.getElem?_Usize_eq]
      simp only [hterms.terms_values]
      simp
    have hx : x = hterms.call2.term := Result.ok.inj (hread.symm.trans hslot)
    simpa [hx] using hterms.call2.term_canonical
  · have heq : j = 3#usize := usize_eq_of_val_eq j 3#usize (by simpa using hj)
    subst j
    have hslot : Array.index_usize hterms.terms 3#usize = .ok hterms.call3.term := by
      unfold Array.index_usize
      simp only [Array.getElem?_Usize_eq]
      simp only [hterms.terms_values]
      simp
    have hx : x = hterms.call3.term := Result.ok.inj (hread.symm.trans hslot)
    simpa [hx] using hterms.call3.term_canonical

#print axioms high_terms_returned_array_reads_canonical

end AspisR1S9HighTermsArrayCanonicalV1
