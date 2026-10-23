import S3S9ScalarFactorFourFoldV1

set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1S9ScalarFactorFourFoldMeaningV1

abbrev Ops := AspisR1S9HelperP6.FieldOps
abbrev S := AspisR1S9HelperP6.field.WideExact
abbrev Q := AspisR1S9HelperP6.field.QM31
abbrev U := Std.Usize
abbrev C := AspisR1S9HelperP6.weights.Weights.scalar_factor.closure
abbrev CanonicalS := AspisR1S9CurrentFieldOpsV1.Canonical
abbrev DecodeS := AspisR1S9CurrentFieldOpsV1.decode
abbrev E := AspisWideTower.WideExact

private theorem bind_ok_inv {α β : Type} {r : Result α} {f : α → Result β}
    {x : β} (h : Bind.bind r f = .ok x) :
    ∃ a, r = .ok a ∧ f a = .ok x := by
  cases r with
  | ok a => exact ⟨a, rfl, h⟩
  | fail e => simp [Bind.bind] at h
  | div => simp [Bind.bind] at h

def contribution (p : S) (q : Q) : E :=
  ⟨AspisR1CurrentWide.Proof.decodeQM
      (AspisR1S9GeneratedWideMulQM31V2.toQM p.c0) *
    AspisR1CurrentWide.Proof.decodeQM
      (AspisR1S9GeneratedWideMulQM31V2.toQM q),
   AspisR1CurrentWide.Proof.decodeQM
      (AspisR1S9GeneratedWideMulQM31V2.toQM p.c1) *
    AspisR1CurrentWide.Proof.decodeQM
      (AspisR1S9GeneratedWideMulQM31V2.toQM q)⟩

/-- A successful emitted scalar-factor callback exposes the three real array
reads and satisfies the installed QM31-multiply/WideExact-add law. -/
theorem scalarStep_actual_meaning
    (ops : Ops) (p : Array S 4#usize) (f : Array Q 4#usize)
    (acc z : S) (i : U)
    (c' : C)
    (h : (letI : Ops := AspisR1S9ScalarFactorActualOpsStepV1.installActualFactorOps ops;
      AspisR1S9ScalarFactorFourFoldV1.scalarStep
        AspisR1S9HelperP6.weights.Weights.scalar_factor.closure.Insts.CoreOpsFunctionFnMutPairWideExactUsizeWideExact
        (acc, (p, f)) i) = .ok (z, c'))
    (hacc : CanonicalS acc)
    (hpvalues : ∀ (index : U) (x : S),
      Array.index_usize p index = .ok x → CanonicalS x)
    (hqvalues : ∀ (index : U) (x : Q),
      Array.index_usize f index = .ok x →
        AspisR1CurrentWide.Proof.CanonicalQM
          (AspisR1S9GeneratedWideMulQM31V2.toQM x)) :
    c' = (p, f) ∧ ∃ j pv qv,
      Array.index_usize AspisR1S9HelperP6.weights.PERM i = .ok j ∧
      Array.index_usize p j = .ok pv ∧ Array.index_usize f i = .ok qv ∧
      CanonicalS z ∧ DecodeS z = DecodeS acc + contribution pv qv := by
  unfold AspisR1S9ScalarFactorFourFoldV1.scalarStep at h
  rcases bind_ok_inv h with ⟨pair, hcall, hret⟩
  rcases pair with ⟨value, closure'⟩
  have hpair : (value, closure') = (z, c') := Result.ok.inj hret
  have hvalue : value = z := congrArg Prod.fst hpair
  have hclosure : closure' = c' := congrArg Prod.snd hpair
  subst value
  subst closure'
  letI : Ops := AspisR1S9ScalarFactorActualOpsStepV1.installActualFactorOps ops
  have hdispatch := AspisR1S9ScalarFactorActualOpsStepV1.scalar_factor_call_mut_dispatch
    ops (p, f) (acc, i)
  have hbody := hcall
  change AspisR1S9HelperP6.weights.Weights.scalar_factor.closure.Insts.CoreOpsFunctionFnMutPairWideExactUsizeWideExact.call_mut
    (p, f) (acc, i) = .ok (z, c') at hbody
  rw [hdispatch] at hbody
  change (do
    let permIndex ← Array.index_usize AspisR1S9HelperP6.weights.PERM i
    let we ← Array.index_usize p permIndex
    let q ← Array.index_usize f i
    let we1 ← AspisR1S9GeneratedWideMulQM31V2.actualHelperOperation we q
    let we2 ← AspisR1S9CurrentFieldOpsV1.actualWideAdd acc we1
    ok (we2, (p, f))) = .ok (z, c') at hbody
  rcases bind_ok_inv hbody with ⟨j, hperm, hbody⟩
  rcases bind_ok_inv hbody with ⟨pv, hp, hbody⟩
  rcases bind_ok_inv hbody with ⟨qv, hq, hbody⟩
  rcases bind_ok_inv hbody with ⟨_mulOut, _hmul, hbody⟩
  rcases bind_ok_inv hbody with ⟨_sumOut, _hadd, hbody⟩
  have hlast : (_sumOut, (p, f)) = (z, c') := Result.ok.inj hbody
  have hz : _sumOut = z := congrArg Prod.fst hlast
  have hc' : c' = (p, f) := (congrArg Prod.snd hlast).symm
  subst _sumOut
  subst c' 
  have hpv : CanonicalS pv := hpvalues j pv hp
  have hqv' : AspisR1CurrentWide.Proof.CanonicalQM
      (AspisR1S9GeneratedWideMulQM31V2.toQM qv) := hqvalues i qv hq
  have hmeaning := AspisR1S9ScalarFactorFoldStepV1.scalar_factor_call_mut_step_sound
    ops (p, f) acc pv qv i j z hperm hp hq hacc hpv hqv' hcall
  exact ⟨rfl, j, pv, qv, hperm, hp, hq, hmeaning.1,
    by simpa [contribution] using hmeaning.2⟩

/-- Successful scalar_factor under the accepted range-fold model is the exact
four-term decoded accumulator followed by the current M31 quarter multiply.
The only iterator/source boundary is the explicit P6 fold law. -/
theorem scalar_factor_success_four_term_meaning
    (ops : Ops) (p : Array S 4#usize) (f : Array Q 4#usize) (out : S)
    (hfold : AspisR1S9HelperP6.IteratorFoldRangeP6Law
      (AspisR1S9ScalarFactorActualOpsStepV1.installActualFactorOps ops))
    (h : (letI : Ops := AspisR1S9ScalarFactorActualOpsStepV1.installActualFactorOps ops
      AspisR1S9HelperP6.weights.Weights.scalar_factor f p) = .ok out)
    (hzeroCan : CanonicalS AspisR1S9HelperP6.field.WideExact.ZERO)
    (hzeroDecode : DecodeS AspisR1S9HelperP6.field.WideExact.ZERO = 0)
    (hpvalues : ∀ (index : U) (x : S),
      Array.index_usize p index = .ok x → CanonicalS x)
    (hqvalues : ∀ (index : U) (x : Q),
      Array.index_usize f index = .ok x →
        AspisR1CurrentWide.Proof.CanonicalQM
          (AspisR1S9GeneratedWideMulQM31V2.toQM x)) :
    ∃ (we : S) (j0 j1 j2 j3 : U)
      (p0 p1 p2 p3 : S) (q0 q1 q2 q3 : Q),
      AspisR1CurrentWide.Proof.CanonicalWide
        (AspisR1S9CurrentFieldOpsV1.toE we) ∧
      Array.index_usize AspisR1S9HelperP6.weights.PERM 0#usize = .ok j0 ∧
      Array.index_usize p j0 = .ok p0 ∧ Array.index_usize f 0#usize = .ok q0 ∧
      Array.index_usize AspisR1S9HelperP6.weights.PERM 1#usize = .ok j1 ∧
      Array.index_usize p j1 = .ok p1 ∧ Array.index_usize f 1#usize = .ok q1 ∧
      Array.index_usize AspisR1S9HelperP6.weights.PERM 2#usize = .ok j2 ∧
      Array.index_usize p j2 = .ok p2 ∧ Array.index_usize f 2#usize = .ok q2 ∧
      Array.index_usize AspisR1S9HelperP6.weights.PERM 3#usize = .ok j3 ∧
      Array.index_usize p j3 = .ok p3 ∧ Array.index_usize f 3#usize = .ok q3 ∧
      AspisR1CurrentWide.Proof.decodeWide
        (AspisR1S9CurrentFieldOpsV1.toE out) =
        (((((0 : E) + contribution p0 q0) + contribution p1 q1) +
            contribution p2 q2) + contribution p3 q3) *
          AspisR1CurrentWide.Proof.wideScalarEmbedding
            AspisR1S9HelperP6.weights.QUARTER := by
  letI : Ops := AspisR1S9ScalarFactorActualOpsStepV1.installActualFactorOps ops
  obtain ⟨we, s0, s1, s2, hmul, h0, h1, h2, h3⟩ :=
    AspisR1S9ScalarFactorFourFoldV1.scalar_factor_success_four_fold_calls
      ops f p out hfold h
  have h0m := scalarStep_actual_meaning ops p f
    AspisR1S9HelperP6.field.WideExact.ZERO s0.1 0#usize s0.2
    (by simpa using h0) hzeroCan hpvalues hqvalues
  rcases h0m with ⟨hs0c, j0, p0, q0, hperm0, hp0, hq0, hc0, hd0⟩
  have h1' := h1
  change AspisR1S9ScalarFactorFourFoldV1.scalarStep
    AspisR1S9HelperP6.weights.Weights.scalar_factor.closure.Insts.CoreOpsFunctionFnMutPairWideExactUsizeWideExact
    (s0.1, s0.2) 1#usize = .ok s1 at h1'
  rw [hs0c] at h1'
  have h1m := scalarStep_actual_meaning ops p f s0.1 s1.1 1#usize s1.2
    (by simpa using h1') hc0 hpvalues hqvalues
  rcases h1m with ⟨hs1c, j1, p1, q1, hperm1, hp1, hq1, hc1, hd1⟩
  have h2' := h2
  change AspisR1S9ScalarFactorFourFoldV1.scalarStep
    AspisR1S9HelperP6.weights.Weights.scalar_factor.closure.Insts.CoreOpsFunctionFnMutPairWideExactUsizeWideExact
    (s1.1, s1.2) 2#usize = .ok s2 at h2'
  rw [hs1c] at h2'
  have h2m := scalarStep_actual_meaning ops p f s1.1 s2.1 2#usize s2.2
    (by simpa using h2') hc1 hpvalues hqvalues
  rcases h2m with ⟨hs2c, j2, p2, q2, hperm2, hp2, hq2, hc2, hd2⟩
  have h3' := h3
  change AspisR1S9ScalarFactorFourFoldV1.scalarStep
    AspisR1S9HelperP6.weights.Weights.scalar_factor.closure.Insts.CoreOpsFunctionFnMutPairWideExactUsizeWideExact
    (s2.1, s2.2) 3#usize = .ok (we, (p, f)) at h3'
  rw [hs2c] at h3'
  have h3m := scalarStep_actual_meaning ops p f s2.1 we 3#usize (p, f)
    (by simpa using h3') hc2 hpvalues hqvalues
  rcases h3m with ⟨_hs3c, j3, p3, q3, hperm3, hp3, hq3, hc3, hd3⟩
  have hquarter := AspisR1S9CurrentFieldOpsV1.actualWideMulM31_success we out
    AspisR1S9HelperP6.weights.QUARTER hc3 hmul
  have hdecodeWe : DecodeS we =
      ((((0 : E) + contribution p0 q0) + contribution p1 q1) +
        contribution p2 q2) + contribution p3 q3 := by
    calc
      DecodeS we = DecodeS s2.1 + contribution p3 q3 := hd3
      _ = (DecodeS s1.1 + contribution p2 q2) + contribution p3 q3 := by rw [hd2]
      _ = ((DecodeS s0.1 + contribution p1 q1) + contribution p2 q2) +
          contribution p3 q3 := by rw [hd1]
      _ = (((DecodeS AspisR1S9HelperP6.field.WideExact.ZERO + contribution p0 q0) +
            contribution p1 q1) + contribution p2 q2) + contribution p3 q3 := by rw [hd0]
      _ = _ := by rw [hzeroDecode]
  refine ⟨we, j0, j1, j2, j3, p0, p1, p2, p3, q0, q1, q2, q3,
    ?_, hperm0, hp0, hq0, hperm1, hp1, hq1, hperm2, hp2, hq2, hperm3, hp3, hq3, ?_⟩
  · change CanonicalS we
    exact hc3
  · change AspisR1S9CurrentFieldOpsV1.decode out = _
    rw [hquarter.2]
    change AspisR1S9CurrentFieldOpsV1.decode we * _ = _
    change AspisR1S9CurrentFieldOpsV1.decode we = _ at hdecodeWe
    rw [hdecodeWe]

#print axioms scalarStep_actual_meaning
#print axioms scalar_factor_success_four_term_meaning

end AspisR1S9ScalarFactorFourFoldMeaningV1
