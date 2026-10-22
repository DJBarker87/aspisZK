import S9CandidatePowersTotalV1
import S9CandidateScalarFactorTotalV1
import S9CandidateHighArraySemanticsV1
import S9HighTermsTraceV1
import S9ConcreteScalarCallSemanticsV1
import S3S9ConcreteSquareSemanticsV1
import S9QMMulTotalCanonicalV1

set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1S9CandidateArithmeticPrefixV1

abbrev CQ := AspisR1S9CandidateHelperV1.field.QM31
abbrev CW := AspisR1S9CandidateHelperV1.field.WideExact
abbrev PQ := AspisR1S9HelperP6.field.QM31
abbrev PW := AspisR1S9HelperP6.field.WideExact
abbrev U := Std.Usize
abbrev mapArray {A B : Type} {N : Usize} (f : A → B) (a : Array A N) : Array B N :=
  AspisR1S9CandidateFoldMapPrimitivesV1.mapArray f a
abbrev ccan (x : CQ) : Prop :=
  AspisR1CurrentWide.Proof.CanonicalQM
    (AspisR1S9HelperP6PowerSemanticsV1.helperToCurrentQM
      (AspisR1S9CandidateHelperV1.toP6Q x))
abbrev pcanon (x : PQ) : Prop :=
  AspisR1CurrentWide.Proof.CanonicalQM
    (AspisR1S9GeneratedWideMulQM31V2.toQM x)
abbrev cdecodeW (x : CW) :=
  AspisR1CurrentWide.Proof.CanonicalWide
    (AspisR1S9GeneratedWideMulQM31V2.toWide (AspisR1S9CandidateHelperV1.toP6W x))
abbrev pdecodeW (x : PW) :=
  AspisR1CurrentWide.Proof.CanonicalWide
    (AspisR1S9GeneratedWideMulQM31V2.toWide x)

private theorem generated_current (x : PQ) :
    AspisR1S9GeneratedWideMulQM31V2.toQM x =
      AspisR1S9HelperP6PowerSemanticsV1.helperToCurrentQM x := by
  cases x <;> rfl

private theorem candidate_canonical_generated (x : CQ) (hx : ccan x) :
    pcanon (AspisR1S9CandidateHelperV1.toP6Q x) := by
  change AspisR1CurrentWide.Proof.CanonicalQM
    (AspisR1S9GeneratedWideMulQM31V2.toQM
      (AspisR1S9CandidateHelperV1.toP6Q x))
  rw [generated_current]
  exact hx

private theorem index_success_bound {A : Type} {N : Std.Usize}
    (a : Array A N) (i : U) (x : A)
    (h : Array.index_usize a i = .ok x) : i.val < N.val := by
  unfold Array.index_usize at h
  cases hopt : a[i]? with
  | none => simp [hopt] at h
  | some y =>
      have hsome : a.val[i.val]? = some y := by simpa using hopt
      have hlen : i.val < a.val.length := (List.getElem?_eq_some_iff.mp hsome).1
      simpa only [a.property] using hlen

private theorem one_canonical : ccan AspisR1S9CandidateHelperV1.field.QM31.ONE := by
  change @AspisR1S9HelperP6PowerSemanticsV1.QMSemantics.canonical
    AspisR1CurrentWide.Proof.ExactQM _
    AspisR1S9HelperP6PowerSemanticsV1.currentFieldOps
    AspisR1S9HelperP6PowerSemanticsV1.currentQMSemantics
    (AspisR1S9CandidateHelperV1.toP6Q
      AspisR1S9CandidateHelperV1.field.QM31.ONE)
  have hone : AspisR1S9CandidateHelperV1.toP6Q
      AspisR1S9CandidateHelperV1.field.QM31.ONE =
      AspisR1S9HelperP6.field.QM31.ONE := by
    unfold AspisR1S9CandidateHelperV1.toP6Q
      AspisR1S9CandidateHelperV1.toP6CM AspisR1S9CandidateHelperV1.toP6M
      AspisR1S9CandidateHelperV1.field.QM31.ONE AspisR1S9HelperP6.field.QM31.ONE
    rfl
  rw [hone]
  exact @AspisR1S9HelperP6PowerSemanticsV1.QMSemantics.one_canonical
    AspisR1CurrentWide.Proof.ExactQM _
    AspisR1S9HelperP6PowerSemanticsV1.currentFieldOps
    AspisR1S9HelperP6PowerSemanticsV1.currentQMSemantics

private theorem candidate_mul_total
    (x y : CQ) (hx : ccan x) (hy : ccan y) :
    ∃ z : CQ, AspisR1S9CandidateHelperV1.field.QM31.mul x y = .ok z ∧ ccan z := by
  obtain ⟨zp, hp, hcp⟩ := AspisR1S9QMMulTotalCanonicalV1.concrete_qm_mul_total
    (AspisR1S9CandidateHelperV1.toP6Q x) (AspisR1S9CandidateHelperV1.toP6Q y) hx hy
  have hm := AspisR1S9CandidateHelperBridgeV1.map_qm_mul x y
  rw [hp] at hm
  cases hc : AspisR1S9CandidateHelperV1.field.QM31.mul x y with
  | ok z =>
      have hz : AspisR1S9CandidateHelperV1.toP6Q z = zp := by
        have heq : Result.ok (AspisR1S9CandidateHelperV1.toP6Q z) = Result.ok zp := by
          simpa only [AspisR1S9CandidateHelperBridgeV1.mapResult, hc] using hm
        exact Result.ok.inj heq
      refine ⟨z, rfl, ?_⟩
      change AspisR1CurrentWide.Proof.CanonicalQM
        (AspisR1S9HelperP6PowerSemanticsV1.helperToCurrentQM
          (AspisR1S9CandidateHelperV1.toP6Q z))
      rw [hz]
      exact hcp
  | fail e =>
      simp only [hc, AspisR1S9CandidateHelperBridgeV1.mapResult] at hm
      cases hm
  | div =>
      simp only [hc, AspisR1S9CandidateHelperBridgeV1.mapResult] at hm
      cases hm

private theorem candidate_square_total
    (x : CQ) (hx : ccan x) :
    ∃ z : CQ, AspisR1S9CandidateHelperV1.field.QM31.square x = .ok z ∧ ccan z := by
  obtain ⟨zp, hp, hcp, _⟩ :=
    AspisR1S9ConcreteSquareSemanticsV1.concrete_qmSquare_total
      (AspisR1S9CandidateHelperV1.toP6Q x) hx
  have hm := AspisR1S9CandidateHelperBridgeV1.map_qm_square x
  rw [hp] at hm
  cases hc : AspisR1S9CandidateHelperV1.field.QM31.square x with
  | ok z =>
      have hz : AspisR1S9CandidateHelperV1.toP6Q z = zp := by
        have heq : Result.ok (AspisR1S9CandidateHelperV1.toP6Q z) = Result.ok zp := by
          simpa only [AspisR1S9CandidateHelperBridgeV1.mapResult, hc] using hm
        exact Result.ok.inj heq
      refine ⟨z, rfl, ?_⟩
      change AspisR1CurrentWide.Proof.CanonicalQM
        (AspisR1S9HelperP6PowerSemanticsV1.helperToCurrentQM
          (AspisR1S9CandidateHelperV1.toP6Q z))
      rw [hz]
      exact hcp
  | fail e =>
      simp only [hc, AspisR1S9CandidateHelperBridgeV1.mapResult] at hm
      cases hm
  | div =>
      simp only [hc, AspisR1S9CandidateHelperBridgeV1.mapResult] at hm
      cases hm

private theorem map_read_canonical
    (a : Array CQ (4#usize)) (i : U) (x : CQ)
    (h : Array.index_usize a i = .ok x)
    (hc : ccan x) :
    pcanon (AspisR1S9CandidateHelperV1.toP6Q x) := by
  change AspisR1CurrentWide.Proof.CanonicalQM
    (AspisR1S9GeneratedWideMulQM31V2.toQM
      (AspisR1S9CandidateHelperV1.toP6Q x))
  rw [generated_current]
  exact hc

/-- The arithmetic prefix returned by the generated candidate helper. `q4mul`
retains the fourth explicit multiplication (whose result is unused by the
source); `q4` is the subsequent index-2 read from the exact three-power array.
The P6 high-term callback witness is built from canonical reads, rather than
supplied as a successful `from_fn` premise. -/
structure CandidateArithmeticPrefix
    (ap0 ap1 : Array CW (4#usize)) (extra : Array CQ (2#usize)) (side : U) where
  seed : CQ
  q1 : CQ
  q2 : CQ
  q3 : CQ
  q4mul : CQ
  q4 : CQ
  q41 : CQ
  q8 : CQ
  q12 : CQ
  q16 : CQ
  q4_canonical : pcanon (AspisR1S9CandidateHelperV1.toP6Q q4)
  q41_canonical : pcanon (AspisR1S9CandidateHelperV1.toP6Q q41)
  q16_canonical : pcanon (AspisR1S9CandidateHelperV1.toP6Q q16)
  low : CW
  low_canonical : AspisR1S9CurrentFieldOpsV1.Canonical
    (AspisR1S9CandidateHelperV1.toP6W low)
  highTerms : AspisR1S9HighTermsTraceV1.HighTermsFour
    (mapArray AspisR1S9CandidateHelperV1.toP6W ap1)
    (mapArray AspisR1S9CandidateHelperV1.toP6Q
      (AspisR1S9CandidateBodyTermsV1.candidateHigh q41 q8 q12))
  seed_canonical : ccan seed
  seed_read : Array.index_usize extra side = .ok seed
  mul1 : AspisR1S9CandidateHelperV1.field.QM31.mul
    AspisR1S9CandidateHelperV1.field.QM31.ONE seed = .ok q1
  mul2 : AspisR1S9CandidateHelperV1.field.QM31.mul q1 seed = .ok q2
  mul3 : AspisR1S9CandidateHelperV1.field.QM31.mul q2 seed = .ok q3
  mul4 : AspisR1S9CandidateHelperV1.field.QM31.mul q3 seed = .ok q4mul
  q4_read : Array.index_usize
    (Array.make 4#usize [AspisR1S9CandidateHelperV1.field.QM31.ONE,q1,q2,q3])
    2#usize = .ok q4
  square41 : AspisR1S9CandidateHelperV1.field.QM31.square q4 = .ok q41
  square8 : AspisR1S9CandidateHelperV1.field.QM31.square q41 = .ok q8
  mul12 : AspisR1S9CandidateHelperV1.field.QM31.mul q8 q41 = .ok q12
  square16 : AspisR1S9CandidateHelperV1.field.QM31.square q8 = .ok q16
  scalar : AspisR1S9CandidateHelperV1.weights.Weights.scalar_factor
    (Array.make 4#usize [AspisR1S9CandidateHelperV1.field.QM31.ONE,q1,q2,q3]) ap0 = .ok low
  scalar_mapped : @AspisR1S9HelperP6.weights.Weights.scalar_factor
      AspisR1S9ConcreteFieldOpsV1.concreteFieldOps
      (mapArray AspisR1S9CandidateHelperV1.toP6Q
        (Array.make 4#usize [AspisR1S9CandidateHelperV1.field.QM31.ONE,q1,q2,q3]))
      (mapArray AspisR1S9CandidateHelperV1.toP6W ap0) =
      .ok (AspisR1S9CandidateHelperV1.toP6W low)

/-- From actual candidate input arrays whose mapped cells are canonical, the
source-ordered arithmetic prefix and P6 high-term callback are total. -/
theorem candidate_arithmetic_prefix_total
    (ap0 ap1 : Array CW (4#usize)) (extra : Array CQ (2#usize)) (side : U)
    (hside : side.val < 2)
    (hap0 : ∀ (j : U) (x : PW),
      Array.index_usize (mapArray AspisR1S9CandidateHelperV1.toP6W ap0) j = .ok x →
      AspisR1S9CurrentFieldOpsV1.Canonical x)
    (hap1 : ∀ (j : U) (x : PW),
      Array.index_usize (mapArray AspisR1S9CandidateHelperV1.toP6W ap1) j = .ok x →
      AspisR1S9HighTermsTraceV1.canonicalW x)
    (hextra : ∀ (j : U) (x : PQ),
      Array.index_usize (mapArray AspisR1S9CandidateHelperV1.toP6Q extra) j = .ok x →
      AspisR1CurrentWide.Proof.CanonicalQM
        (AspisR1S9HelperP6PowerSemanticsV1.helperToCurrentQM x)) :
    Nonempty (CandidateArithmeticPrefix ap0 ap1 extra side) := by
  have htwo : (2#usize).val = 2 := by decide
  obtain ⟨seed, hseed, _⟩ := WP.spec_imp_exists
    (Array.index_usize_spec extra side
      (by simpa [extra.property, htwo] using hside))
  have hseedMapped : Array.index_usize
      (mapArray AspisR1S9CandidateHelperV1.toP6Q extra) side =
        .ok (AspisR1S9CandidateHelperV1.toP6Q seed) := by
    have hm := AspisR1S9CandidateFoldMapPrimitivesV1.mapArray_index_result
      AspisR1S9CandidateHelperV1.toP6Q extra side
    rw [hseed] at hm
    simpa only [AspisR1S9CandidateFoldMapPrimitivesV1.mapResult] using hm.symm
  have hseedCan : ccan seed := hextra side (AspisR1S9CandidateHelperV1.toP6Q seed) hseedMapped
  obtain ⟨q1,q2,q3,q4mul,values,h1,h2,h3,h4,hc1,hc2,hc3,hc4,hvalues,hlist,hvaluesCan⟩ :=
    AspisR1S9CandidatePowersTotalV1.candidate_powers4_total seed hseedCan
  let f : Array CQ (4#usize) :=
    Array.make 4#usize [AspisR1S9CandidateHelperV1.field.QM31.ONE,q1,q2,q3]
  have hq4 : Array.index_usize f 2#usize = .ok q2 := by
    simp [f, Array.index_usize, Array.make]
  have hvaluesConcrete : @AspisR1S9HelperP6.weights.kpowers
      AspisR1S9ConcreteFieldOpsV1.concreteFieldOps (4#usize)
      (AspisR1S9CandidateHelperV1.toP6Q seed) = .ok values := by
    simpa only [AspisR1S9HelperP6PowerSemanticsV1.currentFieldOps] using
      (AspisR1S9ConcreteFieldOpsV1.kpowers_concrete_eq_current
        (4#usize) (AspisR1S9CandidateHelperV1.toP6Q seed)).trans hvalues
  obtain ⟨q41,hq41,hc41⟩ := candidate_square_total q2 hc2
  obtain ⟨q8,hq8,hc8⟩ := candidate_square_total q41 hc41
  obtain ⟨q12,hq12,hc12⟩ := candidate_mul_total q8 q41 hc8 hc41
  obtain ⟨q16,hq16,hc16⟩ := candidate_square_total q8 hc8
  have hq4Can : pcanon (AspisR1S9CandidateHelperV1.toP6Q q2) :=
    candidate_canonical_generated q2 hc2
  have hq41Can : pcanon (AspisR1S9CandidateHelperV1.toP6Q q41) :=
    candidate_canonical_generated q41 hc41
  have hq16Can : pcanon (AspisR1S9CandidateHelperV1.toP6Q q16) :=
    candidate_canonical_generated q16 hc16
  have hseedGen : AspisR1S9CandidateHighArraySemanticsV1.CanonicalP6
      (AspisR1S9CandidateHelperV1.toP6Q seed) := by
    change AspisR1CurrentWide.Proof.CanonicalQM
      (AspisR1S9GeneratedWideMulQM31V2.toQM
        (AspisR1S9CandidateHelperV1.toP6Q seed))
    rw [generated_current]
    exact hseedCan
  have hhigh := AspisR1S9CandidateHighArraySemanticsV1.candidate_high_array_canonical
    seed q1 q2 q3 q2 q41 q8 q12 hseedGen h1 h2 h3 hq4 hq41 hq8 hq12
  have hf : ∀ (j : U) (x : PQ),
      Array.index_usize (mapArray AspisR1S9CandidateHelperV1.toP6Q f) j = .ok x →
      AspisR1CurrentWide.Proof.CanonicalQM
        (AspisR1S9GeneratedWideMulQM31V2.toQM x) := by
    intro j x hread
    have hm := AspisR1S9CandidateFoldMapPrimitivesV1.mapArray_index_result
      AspisR1S9CandidateHelperV1.toP6Q f j
    rw [hread] at hm
    cases hs : Array.index_usize f j with
    | ok y =>
        have hy : AspisR1S9CandidateHelperV1.toP6Q y = x := by
          have heq : Result.ok (AspisR1S9CandidateHelperV1.toP6Q y) = .ok x := by
            simpa only [AspisR1S9CandidateFoldMapPrimitivesV1.mapResult, hs] using hm
          exact Result.ok.inj heq
        subst x
        have hjbound : j.val < 4 := by
          have hb := index_success_bound f j y hs
          simpa [f.property] using hb
        have hjcases : j.val = 0 ∨ j.val = 1 ∨ j.val = 2 ∨ j.val = 3 := by omega
        rcases hjcases with hj | hj | hj | hj
        · have heq : j = 0#usize := by apply UScalar.eq_of_val_eq; simpa using hj
          subst j
          have hy1 : y = AspisR1S9CandidateHelperV1.field.QM31.ONE := by
            have hs0 : Array.index_usize f 0#usize = .ok AspisR1S9CandidateHelperV1.field.QM31.ONE := by
              simp [f, Array.index_usize, Array.make]
            exact Result.ok.inj (hs.symm.trans hs0)
          subst y
          exact candidate_canonical_generated
            AspisR1S9CandidateHelperV1.field.QM31.ONE one_canonical
        · have heq : j = 1#usize := by apply UScalar.eq_of_val_eq; simpa using hj
          subst j
          have hs1 : Array.index_usize f 1#usize = .ok q1 := by simp [f, Array.index_usize, Array.make]
          have hy1 : y = q1 := Result.ok.inj (hs.symm.trans hs1)
          subst y
          exact candidate_canonical_generated q1 hc1
        · have heq : j = 2#usize := by apply UScalar.eq_of_val_eq; simpa using hj
          subst j
          have hs2 : Array.index_usize f 2#usize = .ok q2 := hq4
          have hy1 : y = q2 := Result.ok.inj (hs.symm.trans hs2)
          subst y
          exact candidate_canonical_generated q2 hc2
        · have heq : j = 3#usize := by apply UScalar.eq_of_val_eq; simpa using hj
          subst j
          have hs3 : Array.index_usize f 3#usize = .ok q3 := by simp [f, Array.index_usize, Array.make]
          have hy1 : y = q3 := Result.ok.inj (hs.symm.trans hs3)
          subst y
          exact candidate_canonical_generated q3 hc3
    | fail e =>
        simp only [hs, AspisR1S9CandidateFoldMapPrimitivesV1.mapResult] at hm
        cases hm
    | div =>
        simp only [hs, AspisR1S9CandidateFoldMapPrimitivesV1.mapResult] at hm
        cases hm
  obtain ⟨low,hscalar,hscalarMapped⟩ :=
    AspisR1S9CandidateScalarFactorTotalV1.candidate_scalar_factor_total_and_maps f ap0 hap0 hf
  have hmapArrayValues : mapArray AspisR1S9CandidateHelperV1.toP6Q f = values := by
    apply Subtype.ext
    change List.map AspisR1S9CandidateHelperV1.toP6Q f.val = values.val
    simp only [f, Array.make]
    rw [hlist]
    rfl
  have hkpCandidateArray : @AspisR1S9HelperP6.weights.kpowers
      AspisR1S9ConcreteFieldOpsV1.concreteFieldOps (4#usize)
      (AspisR1S9CandidateHelperV1.toP6Q seed) =
      .ok (mapArray AspisR1S9CandidateHelperV1.toP6Q f) := by
    rw [hmapArrayValues]
    exact hvaluesConcrete
  have hlowCan := AspisR1S9ConcreteScalarCallSemanticsV1.concrete_scalar_factor_low_canonical
    (mapArray AspisR1S9CandidateHelperV1.toP6W ap0)
    (mapArray AspisR1S9CandidateHelperV1.toP6Q f)
    (AspisR1S9CandidateHelperV1.toP6W low)
    (AspisR1S9CandidateHelperV1.toP6Q seed)
    hap0 hseedCan hkpCandidateArray hscalarMapped
  have hhighTerms : Nonempty (AspisR1S9HighTermsTraceV1.HighTermsFour
      (mapArray AspisR1S9CandidateHelperV1.toP6W ap1)
      (mapArray AspisR1S9CandidateHelperV1.toP6Q
        (AspisR1S9CandidateBodyTermsV1.candidateHigh q41 q8 q12))) :=
    AspisR1S9HighTermsTraceV1.high_terms4_from_fn_p6
      (mapArray AspisR1S9CandidateHelperV1.toP6W ap1)
      (mapArray AspisR1S9CandidateHelperV1.toP6Q
      (AspisR1S9CandidateBodyTermsV1.candidateHigh q41 q8 q12))
      hap1 hhigh
  exact ⟨⟨seed,q1,q2,q3,q4mul,q2,q41,q8,q12,q16,
    hq4Can,hq41Can,hq16Can,low,hlowCan,Classical.choice hhighTerms,
    hseedCan,hseed,h1,h2,h3,h4,hq4,hq41,hq8,hq12,hq16,hscalar,hscalarMapped⟩⟩

#print axioms candidate_arithmetic_prefix_total

end AspisR1S9CandidateArithmeticPrefixV1
