import S9PairCandidateAfterTermsMapV1

set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1S9PairSideZeroFullCallsV1

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

/-- Invert the complete side-zero `pairAfterTerms` suffix from one successful
execution. The theorem retains both low-times-sum products, the QM multiplier,
and both generated array writes through the exact final output. -/
theorem side_zero_tail_exposes_full_calls
    (ap1 : Array PairW (4#usize)) (iterNext : R)
    (weights : Array PairW (4#usize)) (q41 q8 q12 q16 : PairQ)
    (low : PairW) (perm3 : U) (t0 t1 t2 t3 : PairW)
    (output : Array PairW (4#usize))
    (htail : AspisR1S9PairCandidateAfterTermsMapV1.pairAfterTerms
      ap1 0#usize iterNext weights q41 q8 q12 q16 low perm3 t0 t1 t2 t3 =
      .ok (.cont (iterNext, output))) :
    ∃ (first2 first3 all productAll productFirst3 mixed : PairW)
      (weights1 : Array PairW (4#usize)),
      AspisR1S9PairCallerStepV1.field.WideExact.add t0 t1 = .ok first2 ∧
      AspisR1S9PairCallerStepV1.field.WideExact.add first2 t2 = .ok first3 ∧
      AspisR1S9PairCallerStepV1.field.WideExact.add first3 t3 = .ok all ∧
      AspisR1S9PairCallerStepV1.field.WideExact.mul low all = .ok productAll ∧
      Array.update weights 0#usize productAll = .ok weights1 ∧
      AspisR1S9PairCallerStepV1.field.WideExact.mul low first3 = .ok productFirst3 ∧
      AspisR1S9PairCallerStepV1.field.WideExact.mul_qm31 productFirst3 q16 = .ok mixed ∧
      Array.update weights1 1#usize mixed = .ok output := by
  have hcur := htail
  unfold AspisR1S9PairCandidateAfterTermsMapV1.pairAfterTerms at hcur
  simp only [if_pos rfl] at hcur
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
  rcases bind_success_inv
      (AspisR1S9PairCallerStepV1.field.WideExact.mul low all) _ _ hcur with
    ⟨productAll, hproductAll, hcur⟩
  rcases bind_success_inv (Array.update weights 0#usize productAll) _ _ hcur with
    ⟨weights1, hweights1, hcur⟩
  rcases bind_success_inv
      (AspisR1S9PairCallerStepV1.field.WideExact.mul low first3) _ _ hcur with
    ⟨productFirst3, hproductFirst3, hcur⟩
  rcases bind_success_inv
      (AspisR1S9PairCallerStepV1.field.WideExact.mul_qm31 productFirst3 q16) _ _ hcur with
    ⟨mixed, hmixed, hcur⟩
  rcases bind_success_inv (Array.update weights1 1#usize mixed) _ _ hcur with
    ⟨actualOutput, houtput, hfinal⟩
  have hcontrol := Result.ok.inj hfinal
  have hpair := ControlFlow.cont.inj hcontrol
  have hout : actualOutput = output := congrArg Prod.snd hpair
  subst actualOutput
  exact ⟨first2,first3,all,productAll,productFirst3,mixed,weights1,
    hfirst2,hfirst3,hall,hproductAll,hweights1,hproductFirst3,hmixed,houtput⟩

#print axioms side_zero_tail_exposes_full_calls

end AspisR1S9PairSideZeroFullCallsV1
