import S3PowersToS9ScalarJoinV1
import S3PowersLowTotalV1

set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1S3ScalarFactorTotalV1

abbrev Ops := AspisR1S9HelperP6.FieldOps
abbrev S := AspisR1S9HelperP6.field.WideExact
abbrev Q := AspisR1S9HelperP6.field.QM31
abbrev U := Std.Usize
abbrev W := AspisR1CurrentWide.field.wide_exact.WideExact
abbrev CW := AspisR1CurrentWide.field.QM31

private def fromOld (x : AspisR1CurrentWide.Proof.Old.QM31) : CW :=
  ⟨⟨x.c0.a, x.c0.b⟩, ⟨x.c1.a, x.c1.b⟩⟩

private theorem toQM_fromOld (x : AspisR1CurrentWide.Proof.Old.QM31) :
    AspisR1CurrentWide.Proof.toQM (fromOld x) = x := by cases x <;> rfl

private theorem current_qm_mul_total (x y : CW)
    (hx : AspisR1CurrentWide.Proof.CanonicalQM x)
    (hy : AspisR1CurrentWide.Proof.CanonicalQM y) :
    ∃ z, AspisR1CurrentWide.field.QM31.mul x y = .ok z ∧
      AspisR1CurrentWide.Proof.CanonicalQM z := by
  obtain ⟨raw, hraw, hcan, _⟩ :=
    AspisR1.ExtractedCurrentQM31Exact.current_qm_mul_exact
      (AspisR1CurrentWide.Proof.toQM x) (AspisR1CurrentWide.Proof.toQM y)
      hx hy
  have hsame := AspisR1CurrentWide.Proof.qm_mul_same x y
  rw [hraw] at hsame
  refine ⟨fromOld raw, ?_, ?_⟩
  · cases hmul : AspisR1CurrentWide.field.QM31.mul x y with
    | fail e => simp [hmul] at hsame
    | div => simp [hmul] at hsame
    | ok z =>
        have hz : AspisR1CurrentWide.Proof.toQM z = raw := by
          simpa [hmul, bind_tc_ok] using hsame
        have hback : fromOld (AspisR1CurrentWide.Proof.toQM z) = z := by
          cases z <;> rfl
        have hzback : z = fromOld raw := by
          calc
            z = fromOld (AspisR1CurrentWide.Proof.toQM z) := hback.symm
            _ = fromOld raw := congrArg fromOld hz
        exact congrArg Result.ok hzback
  · change AspisR1CurrentWide.Proof.CanonicalQM
      (fromOld raw)
    change AspisR1.ExtractedCurrentQM31Exact.CurrentCanonicalQM
      (AspisR1CurrentWide.Proof.toQM (fromOld raw))
    rw [toQM_fromOld]
    exact hcan

private theorem current_wide_mul_qm31_total (x : S) (q : Q)
    (hx : AspisR1CurrentWide.Proof.CanonicalWide
      (AspisR1S9GeneratedWideMulQM31V2.toWide x))
    (hq : AspisR1CurrentWide.Proof.CanonicalQM
      (AspisR1S9GeneratedWideMulQM31V2.toQM q)) :
    ∃ z, AspisR1S9HelperP6PowerSemanticsV1.currentWideMulQM31Source x q = .ok z ∧
      AspisR1CurrentWide.Proof.CanonicalWide
        (AspisR1S9HelperP6PowerSemanticsV1.helperToCurrentWide z) := by
  have hx0 : AspisR1CurrentWide.Proof.CanonicalQM
      (AspisR1S9HelperP6PowerSemanticsV1.helperToCurrentQM x.c0) := by
    simpa [AspisR1CurrentWide.Proof.toQM,
      AspisR1S9HelperP6PowerSemanticsV1.helperToCurrentQM,
      AspisR1S9GeneratedWideMulQM31V2.toWide,
      AspisR1S9GeneratedWideMulQM31V2.toQM] using hx.1
  have hx1 : AspisR1CurrentWide.Proof.CanonicalQM
      (AspisR1S9HelperP6PowerSemanticsV1.helperToCurrentQM x.c1) := by
    simpa [AspisR1CurrentWide.Proof.toQM,
      AspisR1S9HelperP6PowerSemanticsV1.helperToCurrentQM,
      AspisR1S9GeneratedWideMulQM31V2.toWide,
      AspisR1S9GeneratedWideMulQM31V2.toQM] using hx.2
  have hq' : AspisR1CurrentWide.Proof.CanonicalQM
      (AspisR1S9HelperP6PowerSemanticsV1.helperToCurrentQM q) := by
    simpa [AspisR1CurrentWide.Proof.toQM,
      AspisR1S9HelperP6PowerSemanticsV1.helperToCurrentQM,
      AspisR1S9GeneratedWideMulQM31V2.toQM] using hq
  obtain ⟨a,ha,hac⟩ := current_qm_mul_total
    (AspisR1S9HelperP6PowerSemanticsV1.helperToCurrentQM x.c0)
    (AspisR1S9HelperP6PowerSemanticsV1.helperToCurrentQM q) hx0 hq'
  obtain ⟨b,hb,hbc⟩ := current_qm_mul_total
    (AspisR1S9HelperP6PowerSemanticsV1.helperToCurrentQM x.c1)
    (AspisR1S9HelperP6PowerSemanticsV1.helperToCurrentQM q) hx1 hq'
  refine ⟨AspisR1S9HelperP6PowerSemanticsV1.currentToHelperWide ⟨a,b⟩, ?_, ?_⟩
  · have hsrc := AspisR1S9HelperP6PowerSemanticsV1.currentWideMulQM31Source_of_canonical x q hq
    have hmul : AspisR1S9HelperP6PowerSemanticsV1.currentWideMulQM31 x q =
        .ok (AspisR1S9HelperP6PowerSemanticsV1.currentToHelperWide ⟨a,b⟩) := by
      simp [AspisR1S9HelperP6PowerSemanticsV1.currentWideMulQM31, ha, hb,
        bind_tc_ok]
    exact hsrc.trans hmul
  · change AspisR1CurrentWide.Proof.CanonicalWide
      (AspisR1S9HelperP6PowerSemanticsV1.helperToCurrentWide
        (AspisR1S9HelperP6PowerSemanticsV1.currentToHelperWide ⟨a,b⟩))
    simp only [AspisR1S9HelperP6PowerSemanticsV1.helperToCurrentWide_currentToHelperWide]
    exact ⟨hac,hbc⟩

theorem actual_helper_mul_total (x : S) (q : Q)
    (hx : AspisR1CurrentWide.Proof.CanonicalWide
      (AspisR1S9GeneratedWideMulQM31V2.toWide x))
    (hq : AspisR1CurrentWide.Proof.CanonicalQM
      (AspisR1S9GeneratedWideMulQM31V2.toQM q)) :
    ∃ z, AspisR1S9GeneratedWideMulQM31V2.actualHelperOperation x q = .ok z ∧
      AspisR1CurrentWide.Proof.CanonicalWide
        (AspisR1S9GeneratedWideMulQM31V2.toWide z) := by
  obtain ⟨z,hz,hzcan⟩ := current_wide_mul_qm31_total x q hx hq
  have heq : AspisR1S9GeneratedWideMulQM31V2.actualHelperOperation x q =
      AspisR1S9HelperP6PowerSemanticsV1.currentWideMulQM31Source x q :=
    (AspisR1S9GeneratedWideMulQM31V2.actualHelperOperation_eq_sourceModel x q).trans
      (AspisR1S9GeneratedWideMulQM31V2.sourceModel_eq_currentSource x q)
  refine ⟨z, ?_, ?_⟩
  · rw [heq]
    exact hz
  · simpa [AspisR1S9GeneratedWideMulQM31V2.toWide,
      AspisR1S9HelperP6PowerSemanticsV1.helperToCurrentWide,
      AspisR1S9GeneratedWideMulQM31V2.toQM,
      AspisR1S9HelperP6PowerSemanticsV1.helperToCurrentQM] using hzcan

private theorem read_array_total {α : Type} (a : Array α (4#usize)) (i : U)
    (hi : i.val < 4) : ∃ x, Array.index_usize a i = .ok x := by
  have hfour : (4#usize).val = 4 := by decide
  obtain ⟨x, hx, _⟩ := WP.spec_imp_exists
    (Array.index_usize_spec a i (by simpa [hfour] using hi))
  exact ⟨x, hx⟩

/-- One actual generated scalar callback always succeeds on an in-range
index when both captured arrays contain canonical values.  The exact field
multiply and add implementations are installed; only the surrounding fold
correspondence remains an explicit standard-library boundary. -/
theorem scalar_step_total
    (ops : Ops) (p : Array S (4#usize)) (f : Array Q (4#usize))
    (acc : S) (i : U)
    (hacc : AspisR1S9CurrentFieldOpsV1.Canonical acc)
    (hp : ∀ (j : U) (x : S), Array.index_usize p j = .ok x →
      AspisR1S9CurrentFieldOpsV1.Canonical x)
    (hf : ∀ (j : U) (x : Q), Array.index_usize f j = .ok x →
      AspisR1CurrentWide.Proof.CanonicalQM
        (AspisR1S9GeneratedWideMulQM31V2.toQM x))
    (hi : i.val < 4) :
    ∃ z, (letI : Ops := AspisR1S9ScalarFactorActualOpsStepV1.installActualFactorOps ops
      AspisR1S9ScalarFactorFourFoldV1.scalarStep
        AspisR1S9HelperP6.weights.Weights.scalar_factor.closure.Insts.CoreOpsFunctionFnMutPairWideExactUsizeWideExact
        (acc, (p, f)) i) = .ok (z, (p, f)) ∧
      AspisR1S9CurrentFieldOpsV1.Canonical z := by
  have hival : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 ∨ i.val = 3 := by omega
  have hpermExists : ∃ k,
      Array.index_usize AspisR1S9HelperP6.weights.PERM i = .ok k ∧ k.val < 4 := by
    rcases hival with hi0 | hi1 | hi2 | hi3
    · have heq : i = 0#usize := Std.UScalar.eq_of_val_eq hi0
      refine ⟨0#usize, ?_⟩
      refine ⟨?_, by decide⟩
      simpa [heq] using AspisR1S9TransparentFoldS2InstanceV1.perm_reads.1
    · have heq : i = 1#usize := Std.UScalar.eq_of_val_eq hi1
      refine ⟨3#usize, ?_⟩
      refine ⟨?_, by decide⟩
      simpa [heq] using AspisR1S9TransparentFoldS2InstanceV1.perm_reads.2.1
    · have heq : i = 2#usize := Std.UScalar.eq_of_val_eq hi2
      refine ⟨2#usize, ?_⟩
      refine ⟨?_, by decide⟩
      simpa [heq] using AspisR1S9TransparentFoldS2InstanceV1.perm_reads.2.2.1
    · have heq : i = 3#usize := Std.UScalar.eq_of_val_eq hi3
      refine ⟨1#usize, ?_⟩
      refine ⟨?_, by decide⟩
      simpa [heq] using AspisR1S9TransparentFoldS2InstanceV1.perm_reads.2.2.2
  obtain ⟨k, hperm, hkbound⟩ := hpermExists
  obtain ⟨pv, hpvread⟩ := read_array_total p k hkbound
  obtain ⟨qv, hqvread⟩ := read_array_total f i hi
  have hpvcan := hp k pv hpvread
  have hqvcan := hf i qv hqvread
  have hpvmap : AspisR1S9CurrentFieldOpsV1.toE pv =
      AspisR1S9GeneratedWideMulQM31V2.toWide pv := by
    cases pv <;> rfl
  have hpvcan' : AspisR1CurrentWide.Proof.CanonicalWide
      (AspisR1S9GeneratedWideMulQM31V2.toWide pv) := by
    change AspisR1CurrentWide.Proof.CanonicalWide
      (AspisR1S9CurrentFieldOpsV1.toE pv) at hpvcan
    rw [hpvmap] at hpvcan
    exact hpvcan
  obtain ⟨mulOut, hmul, hmulCan⟩ := actual_helper_mul_total pv qv
    hpvcan' hqvcan
  obtain ⟨sumOut, hadd, haddCan, _haddVal⟩ :=
    AspisR1S9CurrentFieldOpsV1.actualWideAdd_total_exact acc mulOut hacc hmulCan
  letI : Ops := AspisR1S9ScalarFactorActualOpsStepV1.installActualFactorOps ops
  have hdispatch := AspisR1S9ScalarFactorActualOpsStepV1.scalar_factor_call_mut_dispatch
    ops (p, f) (acc, i)
  have hcall :
      (letI : Ops := AspisR1S9ScalarFactorActualOpsStepV1.installActualFactorOps ops
       AspisR1S9HelperP6.weights.Weights.scalar_factor.closure.Insts.CoreOpsFunctionFnMutPairWideExactUsizeWideExact.call_mut
         (p, f) (acc, i)) = .ok (sumOut, (p, f)) := by
    rw [hdispatch]
    simp [hperm, hpvread, hqvread, hmul, hadd, bind_tc_ok]
  let c : AspisR1S9HelperP6.weights.Weights.scalar_factor.closure := (p, f)
  have hcallC :
      (letI : Ops := AspisR1S9ScalarFactorActualOpsStepV1.installActualFactorOps ops
       AspisR1S9HelperP6.weights.Weights.scalar_factor.closure.Insts.CoreOpsFunctionFnMutPairWideExactUsizeWideExact.call_mut
         c (acc, i)) = .ok (sumOut, c) := by
    simpa [c] using hcall
  have hstep : AspisR1S9ScalarFactorFourFoldV1.scalarStep
      AspisR1S9HelperP6.weights.Weights.scalar_factor.closure.Insts.CoreOpsFunctionFnMutPairWideExactUsizeWideExact
      (acc, c) i = .ok (sumOut, c) := by
    simp [AspisR1S9ScalarFactorFourFoldV1.scalarStep, hcallC]
  refine ⟨sumOut, ?_, haddCan⟩
  simpa [c] using hstep

/-- Constructive success for the exact scalar-factor helper model. The only
remaining Iterator boundary is the separately checked P6 fold law; the four
generated callback invocations, their actual field operations, and the final
quarter multiplication are total from canonical array contents. -/
theorem scalar_factor_total_of_canonical_arrays
    (ops : Ops) (p : Array S (4#usize)) (f : Array Q (4#usize))
    (hfold : AspisR1S9HelperP6.IteratorFoldRangeP6Law
      (AspisR1S9ScalarFactorActualOpsStepV1.installActualFactorOps ops))
    (hp : ∀ (j : U) (x : S), Array.index_usize p j = .ok x →
      AspisR1S9CurrentFieldOpsV1.Canonical x)
    (hf : ∀ (j : U) (x : Q), Array.index_usize f j = .ok x →
      AspisR1CurrentWide.Proof.CanonicalQM
        (AspisR1S9GeneratedWideMulQM31V2.toQM x)) :
    ∃ out, (letI : Ops := AspisR1S9ScalarFactorActualOpsStepV1.installActualFactorOps ops
      AspisR1S9HelperP6.weights.Weights.scalar_factor f p) = .ok out := by
  letI : Ops := AspisR1S9ScalarFactorActualOpsStepV1.installActualFactorOps ops
  let callback := AspisR1S9HelperP6.weights.Weights.scalar_factor.closure.Insts.CoreOpsFunctionFnMutPairWideExactUsizeWideExact
  obtain ⟨a0, h0, hc0⟩ := scalar_step_total ops p f
    AspisR1S9HelperP6.field.WideExact.ZERO 0#usize
    AspisR1S9TransparentFoldS2InstanceV1.zero_canonical hp hf (by decide)
  obtain ⟨a1, h1, hc1⟩ := scalar_step_total ops p f a0 1#usize hc0 hp hf (by decide)
  obtain ⟨a2, h2, hc2⟩ := scalar_step_total ops p f a1 2#usize hc1 hp hf (by decide)
  obtain ⟨a3, h3, hc3⟩ := scalar_step_total ops p f a2 3#usize hc2 hp hf (by decide)
  have hcalls : AspisR1S9ScalarFactorFourFoldV1.fourCalls callback
      (AspisR1S9HelperP6.field.WideExact.ZERO, (p, f)) = .ok (a3, (p, f)) := by
    unfold AspisR1S9ScalarFactorFourFoldV1.fourCalls
    rw [h0]
    simp only [bind_tc_ok]
    rw [h1]
    simp only [bind_tc_ok]
    rw [h2]
    simp only [bind_tc_ok]
    rw [h3]
    simp only [bind_tc_ok]
  have hrange : AspisR1S3S9RangeFoldP6.rangeFoldRun 4
      AspisR1S9ScalarFactorFourFoldV1.range04
      (AspisR1S9ScalarFactorFourFoldV1.scalarStep callback)
      (AspisR1S9HelperP6.field.WideExact.ZERO, (p, f)) =
      .ok (a3, (p, f)) := by
    rw [AspisR1S9ScalarFactorFourFoldV1.rangeFold_fourCalls]
    exact hcalls
  have hfoldEq := hfold callback AspisR1S9ScalarFactorFourFoldV1.range04
    AspisR1S9HelperP6.field.WideExact.ZERO (p, f)
  have hiter : AspisR1S9HelperP6.FieldOps.iterFold
      (core.iter.traits.iterator.IteratorRange core.iter.range.StepUsize)
      AspisR1S9HelperP6.weights.Weights.scalar_factor.closure.Insts.CoreOpsFunctionFnMutPairWideExactUsizeWideExact
      AspisR1S9ScalarFactorFourFoldV1.range04 AspisR1S9HelperP6.field.WideExact.ZERO (p, f) =
      .ok a3 := by
    rw [hfoldEq]
    change AspisR1S9HelperP6.iterFoldRange
      AspisR1S9HelperP6.weights.Weights.scalar_factor.closure.Insts.CoreOpsFunctionFnMutPairWideExactUsizeWideExact
      AspisR1S9ScalarFactorFourFoldV1.range04 AspisR1S9HelperP6.field.WideExact.ZERO (p, f) = .ok a3
    unfold AspisR1S9HelperP6.iterFoldRange
    change (do
      let (value, _) ← AspisR1S3S9RangeFoldP6.rangeFoldRun 4
        AspisR1S9ScalarFactorFourFoldV1.range04
        (AspisR1S9ScalarFactorFourFoldV1.scalarStep callback)
        (AspisR1S9HelperP6.field.WideExact.ZERO, (p, f))
      ok value) = .ok a3
    rw [hrange]
    rfl
  obtain ⟨wideOut, hwide⟩ := AspisR1S3PowersLowTotalV1.wide_mul_m31_total
    (AspisR1S9CurrentFieldOpsV1.toE a3) AspisR1S9HelperP6.weights.QUARTER
  have hquarter : AspisR1S9CurrentFieldOpsV1.actualWideMulM31 a3
      AspisR1S9HelperP6.weights.QUARTER = .ok (AspisR1S9CurrentFieldOpsV1.fromE wideOut) := by
    unfold AspisR1S9CurrentFieldOpsV1.actualWideMulM31
    rw [hwide]
    rfl
  refine ⟨AspisR1S9CurrentFieldOpsV1.fromE wideOut, ?_⟩
  change (do
    let we ← AspisR1S9HelperP6.FieldOps.iterFold
      (core.iter.traits.iterator.IteratorRange core.iter.range.StepUsize)
      AspisR1S9HelperP6.weights.Weights.scalar_factor.closure.Insts.CoreOpsFunctionFnMutPairWideExactUsizeWideExact
      AspisR1S9ScalarFactorFourFoldV1.range04
      AspisR1S9HelperP6.field.WideExact.ZERO (p, f)
    AspisR1S9CurrentFieldOpsV1.actualWideMulM31 we AspisR1S9HelperP6.weights.QUARTER) =
      .ok (AspisR1S9CurrentFieldOpsV1.fromE wideOut)
  rw [hiter]
  simp only [bind_tc_ok, hquarter]

#print axioms actual_helper_mul_total
#print axioms scalar_step_total
#print axioms scalar_factor_total_of_canonical_arrays

end AspisR1S3ScalarFactorTotalV1
