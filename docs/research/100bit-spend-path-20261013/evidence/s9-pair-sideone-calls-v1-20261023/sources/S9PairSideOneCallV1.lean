import S9PairCandidateAfterTermsMapV1

set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1S9PairSideOneCallV1

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

/-- A successful side-one suffix from the exact Pair source body contains all
three ordered term sums and the same-run PERM[3], ap1, scale, multiply, add,
and update calls. No separate child-call success assumptions are supplied. -/
theorem side_one_tail_exposes_calls
    (ap1 : Array PairW (4#usize)) (iterNext : R)
    (weights : Array PairW (4#usize)) (q41 q8 q12 q16 : PairQ)
    (low : PairW) (perm3 : U) (t0 t1 t2 t3 : PairW)
    (flow : ControlFlow (R × Array PairW (4#usize)) (Array PairW (4#usize)))
    (htail : AspisR1S9PairCandidateAfterTermsMapV1.pairAfterTerms
      ap1 1#usize iterNext weights q41 q8 q12 q16 low perm3 t0 t1 t2 t3 =
      .ok flow) :
    ∃ (output : Array PairW (4#usize))
      (first2 first3 all old1 ap1perm quarter weighted sum1 : PairW)
      (weights1 : Array PairW (4#usize))
      (allProduct allScaled : PairW)
      (weights2 : Array PairW (4#usize))
      (first2Product first2Scaled : PairW) (q10 : PairQ),
      AspisR1S9PairCallerStepV1.field.WideExact.add t0 t1 = .ok first2 ∧
      AspisR1S9PairCallerStepV1.field.WideExact.add first2 t2 = .ok first3 ∧
      AspisR1S9PairCallerStepV1.field.WideExact.add first3 t3 = .ok all ∧
      Array.index_usize weights 1#usize = .ok old1 ∧
      Array.index_usize ap1 perm3 = .ok ap1perm ∧
      AspisR1S9PairCallerStepV1.field.WideExact.mul_m31 ap1perm
        AspisR1S9PairCallerStepV1.weights.QUARTER = .ok quarter ∧
      AspisR1S9PairCallerStepV1.field.WideExact.mul low quarter = .ok weighted ∧
      AspisR1S9PairCallerStepV1.field.WideExact.add old1 weighted = .ok sum1 ∧
      Array.update weights 1#usize sum1 = .ok weights1 ∧
      AspisR1S9PairCallerStepV1.field.WideExact.mul low all = .ok allProduct ∧
      AspisR1S9PairCallerStepV1.field.WideExact.mul_qm31 allProduct q41 = .ok allScaled ∧
      Array.update weights1 2#usize allScaled = .ok weights2 ∧
      AspisR1S9PairCallerStepV1.field.WideExact.mul low first2 = .ok first2Product ∧
      AspisR1S9PairCallerStepV1.field.QM31.mul q16 q41 = .ok q10 ∧
      AspisR1S9PairCallerStepV1.field.WideExact.mul_qm31 first2Product q10 = .ok first2Scaled ∧
      flow = .cont (iterNext, output) ∧
      Array.update weights2 3#usize first2Scaled = .ok output := by
  have hcur := htail
  unfold AspisR1S9PairCandidateAfterTermsMapV1.pairAfterTerms at hcur
  have hside : (1#usize : U) ≠ 0#usize := by decide
  simp only [if_neg hside] at hcur
  rcases bind_success_inv
      (Array.index_usize (Array.make 4#usize [t0,t1,t2,t3]) 0#usize) _ _ hcur with
    ⟨we8, hwe8, hcur⟩
  have hwe8eq : we8 = t0 := by
    have hread : Array.index_usize (Array.make 4#usize [t0,t1,t2,t3]) 0#usize = .ok t0 := by rfl
    exact Result.ok.inj (hwe8.symm.trans hread)
  subst we8
  rcases bind_success_inv
      (Array.index_usize (Array.make 4#usize [t0,t1,t2,t3]) 1#usize) _ _ hcur with
    ⟨we9, hwe9, hcur⟩
  have hwe9eq : we9 = t1 := by
    have hread : Array.index_usize (Array.make 4#usize [t0,t1,t2,t3]) 1#usize = .ok t1 := by rfl
    exact Result.ok.inj (hwe9.symm.trans hread)
  subst we9
  rcases bind_success_inv
      (AspisR1S9PairCallerStepV1.field.WideExact.add t0 t1) _ _ hcur with
    ⟨first2, hfirst2, hcur⟩
  rcases bind_success_inv
      (Array.index_usize (Array.make 4#usize [t0,t1,t2,t3]) 2#usize) _ _ hcur with
    ⟨we10, hwe10, hcur⟩
  have hwe10eq : we10 = t2 := by
    have hread : Array.index_usize (Array.make 4#usize [t0,t1,t2,t3]) 2#usize = .ok t2 := by rfl
    exact Result.ok.inj (hwe10.symm.trans hread)
  subst we10
  rcases bind_success_inv
      (AspisR1S9PairCallerStepV1.field.WideExact.add first2 t2) _ _ hcur with
    ⟨first3, hfirst3, hcur⟩
  rcases bind_success_inv
      (Array.index_usize (Array.make 4#usize [t0,t1,t2,t3]) 3#usize) _ _ hcur with
    ⟨we11, hwe11, hcur⟩
  have hwe11eq : we11 = t3 := by
    have hread : Array.index_usize (Array.make 4#usize [t0,t1,t2,t3]) 3#usize = .ok t3 := by rfl
    exact Result.ok.inj (hwe11.symm.trans hread)
  subst we11
  rcases bind_success_inv
      (AspisR1S9PairCallerStepV1.field.WideExact.add first3 t3) _ _ hcur with
    ⟨all, hall, hcur⟩
  rcases bind_success_inv (Array.index_usize weights 1#usize) _ _ hcur with
    ⟨old1, hold1, hcur⟩
  rcases bind_success_inv (Array.index_usize ap1 perm3) _ _ hcur with
    ⟨ap1perm, hap1perm, hcur⟩
  rcases bind_success_inv
      (AspisR1S9PairCallerStepV1.field.WideExact.mul_m31 ap1perm
        AspisR1S9PairCallerStepV1.weights.QUARTER) _ _ hcur with
    ⟨quarter, hquarter, hcur⟩
  rcases bind_success_inv
      (AspisR1S9PairCallerStepV1.field.WideExact.mul low quarter) _ _ hcur with
    ⟨weighted, hweighted, hcur⟩
  rcases bind_success_inv
      (AspisR1S9PairCallerStepV1.field.WideExact.add old1 weighted) _ _ hcur with
    ⟨sum1, hsum1, hcur⟩
  rcases bind_success_inv (Array.update weights 1#usize sum1) _ _ hcur with
    ⟨weights1, hweights1, hcur⟩
  rcases bind_success_inv
      (AspisR1S9PairCallerStepV1.field.WideExact.mul low all) _ _ hcur with
    ⟨allProduct, hallProduct, hcur⟩
  rcases bind_success_inv
      (AspisR1S9PairCallerStepV1.field.WideExact.mul_qm31 allProduct q41) _ _ hcur with
    ⟨allScaled, hallScaled, hcur⟩
  rcases bind_success_inv (Array.update weights1 2#usize allScaled) _ _ hcur with
    ⟨weights2, hweights2, hcur⟩
  rcases bind_success_inv
      (AspisR1S9PairCallerStepV1.field.WideExact.mul low first2) _ _ hcur with
    ⟨first2Product, hfirst2Product, hcur⟩
  rcases bind_success_inv
      (AspisR1S9PairCallerStepV1.field.QM31.mul q16 q41) _ _ hcur with
    ⟨q10, hq10, hcur⟩
  rcases bind_success_inv
      (AspisR1S9PairCallerStepV1.field.WideExact.mul_qm31 first2Product q10) _ _ hcur with
    ⟨first2Scaled, hfirst2Scaled, hcur⟩
  rcases bind_success_inv (Array.update weights2 3#usize first2Scaled) _ _ hcur with
    ⟨output', houtput, hrest⟩
  let output := output'
  have hflow : flow = ControlFlow.cont (iterNext, output) := (Result.ok.inj hrest).symm
  exact ⟨output, first2, first3, all, old1, ap1perm, quarter, weighted, sum1, weights1,
    allProduct, allScaled, weights2, first2Product, first2Scaled, q10,
    hfirst2, hfirst3, hall, hold1, hap1perm, hquarter, hweighted, hsum1,
    hweights1, hallProduct, hallScaled, hweights2, hfirst2Product, hq10,
    hfirst2Scaled, hflow, houtput⟩

#print axioms side_one_tail_exposes_calls

end AspisR1S9PairSideOneCallV1
