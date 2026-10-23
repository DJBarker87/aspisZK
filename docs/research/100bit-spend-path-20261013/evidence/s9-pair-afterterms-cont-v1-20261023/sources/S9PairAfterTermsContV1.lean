import S9PairCandidateAfterTermsMapV1

set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow

namespace AspisR1S9PairAfterTermsContV1

abbrev PairW := AspisR1S9PairCallerStepV1.field.WideExact
abbrev PairQ := AspisR1S9PairCallerStepV1.field.QM31
abbrev R := AspisR1S9PairCallerBodyPrefixV1.R
abbrev U := Std.Usize

private theorem bind_success_inv {α β : Type} (m : Result α) (k : α → Result β)
    (v : β) (h : (do let x ← m; k x) = .ok v) :
    ∃ x, m = .ok x ∧ k x = .ok v := by
  cases m with
  | ok x => exact ⟨x, rfl, h⟩
  | fail e => simp only [bind_tc_fail] at h; cases h
  | div => simp only [bind_tc_div] at h; cases h

/-- A successful side-zero `pairAfterTerms` necessarily returns the iterator
continuation constructor. This is just inversion of its exact bind sequence;
no child success is assumed. -/
theorem pair_after_terms_success_cont
    (ap1 : Array PairW (4#usize)) (iterNext : R)
    (weights : Array PairW (4#usize)) (q41 q8 q12 q16 : PairQ)
    (low : PairW) (perm3 : U) (t0 t1 t2 t3 : PairW)
    (flow : ControlFlow (R × Array PairW (4#usize)) (Array PairW (4#usize)))
    (h : AspisR1S9PairCandidateAfterTermsMapV1.pairAfterTerms
      ap1 0#usize iterNext weights q41 q8 q12 q16 low perm3 t0 t1 t2 t3 = .ok flow) :
    ∃ out, flow = .cont (iterNext,out) := by
  have hcur := h
  unfold AspisR1S9PairCandidateAfterTermsMapV1.pairAfterTerms at hcur
  simp only [if_pos rfl] at hcur
  rcases bind_success_inv
    (Array.index_usize (Array.make 4#usize [t0,t1,t2,t3]) 0#usize) _ _ hcur with
    ⟨we8, hwe8, hcur⟩
  rcases bind_success_inv
    (Array.index_usize (Array.make 4#usize [t0,t1,t2,t3]) 1#usize) _ _ hcur with
    ⟨we9, hwe9, hcur⟩
  rcases bind_success_inv (AspisR1S9PairCallerStepV1.field.WideExact.add we8 we9) _ _ hcur with
    ⟨first2, hfirst2, hcur⟩
  rcases bind_success_inv
    (Array.index_usize (Array.make 4#usize [t0,t1,t2,t3]) 2#usize) _ _ hcur with
    ⟨we10, hwe10, hcur⟩
  rcases bind_success_inv (AspisR1S9PairCallerStepV1.field.WideExact.add first2 we10) _ _ hcur with
    ⟨first3, hfirst3, hcur⟩
  rcases bind_success_inv
    (Array.index_usize (Array.make 4#usize [t0,t1,t2,t3]) 3#usize) _ _ hcur with
    ⟨we11, hwe11, hcur⟩
  rcases bind_success_inv (AspisR1S9PairCallerStepV1.field.WideExact.add first3 we11) _ _ hcur with
    ⟨all, hall, hcur⟩
  rcases bind_success_inv (AspisR1S9PairCallerStepV1.field.WideExact.mul low all) _ _ hcur with
    ⟨we12, hwe12, hcur⟩
  rcases bind_success_inv (Array.update weights 0#usize we12) _ _ hcur with
    ⟨weights1, hweights1, hcur⟩
  rcases bind_success_inv (AspisR1S9PairCallerStepV1.field.WideExact.mul low first3) _ _ hcur with
    ⟨we13, hwe13, hcur⟩
  rcases bind_success_inv (AspisR1S9PairCallerStepV1.field.WideExact.mul_qm31 we13 q16) _ _ hcur with
    ⟨we14, hwe14, hcur⟩
  rcases bind_success_inv (Array.update weights1 1#usize we14) _ _ hcur with
    ⟨out, hout, hfinal⟩
  have hflow := Result.ok.inj hfinal
  exact ⟨out, hflow.symm⟩

#print axioms pair_after_terms_success_cont

end AspisR1S9PairAfterTermsContV1
