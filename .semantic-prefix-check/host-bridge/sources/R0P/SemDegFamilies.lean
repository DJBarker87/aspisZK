import R0P.SemDeg

/-! Coordinate degree audit of the literal production families. Lists and
folds are handled symbolically, with generated descriptors kept opaque. -/
set_option autoImplicit false
noncomputable section
namespace R0P.SemSource
variable {K : Type} [Field K]

/-- The terminal's three claimed openings, including the exact column casts. -/
def openingsOf (y : Fin 3 → Fin 29 → K) : Openings K :=
  ⟨fun c => y 0 (Fin.castLE (by omega) c), fun c => y 1 (Fin.castLE (by omega) c),
    fun c => y 2 (Fin.castLE (by omega) c)⟩
end R0P.SemSource

namespace R0P.SemDegree
open Polynomial SemSource
attribute [local irreducible] VDeg honestClaims
variable {K : Type} [Field K]

theorem vdeg_openings_z (t : Trace K) (c : Fin 16) :
    VDeg 10 (fun _ => 1) (fun v => (openingsOf (honestClaims t v)).z c) :=
  by
    unfold openingsOf
    exact vdeg_honestClaims_zero t (Fin.castLE (by omega) c)

theorem vdeg_openings_succ (t : Trace K) (c : Fin 16) :
    VDeg 10 (fun i => i.val+1) (fun v => (openingsOf (honestClaims t v)).succ c) :=
  by
    unfold openingsOf
    exact vdeg_honestClaims_one t (Fin.castLE (by omega) c)

theorem vdeg_openings_xor12 (t : Trace K) (c : Fin 16) :
    VDeg 10 (fun _ => 1) (fun v => (openingsOf (honestClaims t v)).xor12 c) :=
  by
    unfold openingsOf
    exact vdeg_honestClaims_two t (Fin.castLE (by omega) c)

#print axioms vdeg_openings_z
#print axioms vdeg_openings_succ
#print axioms vdeg_openings_xor12

/-- Degree of every residual, including the literal zero default. -/
def LDeg (d : Fin 10 → Nat) (L : (Fin 10 → K) → List K) : Prop :=
  ∀ i, VDeg 10 d (fun v => (L v).getD i 0)

theorem ldeg_mono {d e : Fin 10 → Nat} {L : (Fin 10 → K) → List K}
    (h : LDeg d L) (he : ∀ i, d i ≤ e i) : LDeg e L :=
  fun i => vdeg_mono (h i) he

theorem ldeg_nil (d : Fin 10 → Nat) : LDeg d (fun _ : Fin 10 → K => []) := by
  intro i; simpa only [List.getD_nil] using vdeg_const 10 d (0 : K)

theorem ldeg_cons {d : Fin 10 → Nat} (f : (Fin 10 → K) → K)
    (L : (Fin 10 → K) → List K) (hf : VDeg 10 d f) (hL : LDeg d L) :
    LDeg d (fun v => f v :: L v) := by
  intro i
  cases i with
  | zero => simpa using hf
  | succ i => simpa using hL i

theorem ldeg_append {d : Fin 10 → Nat} (L M : (Fin 10 → K) → List K)
    (len : Nat) (hlen : ∀ v, (L v).length = len) (hL : LDeg d L) (hM : LDeg d M) :
    LDeg d (fun v => L v ++ M v) := by
  intro i
  by_cases hi : i < len
  · have he (v : Fin 10 → K) : (L v ++ M v).getD i 0 = (L v).getD i 0 :=
      List.getD_append _ _ _ _ (by rw [hlen]; exact hi)
    simp only [he]; exact hL i
  · have he (v : Fin 10 → K) : (L v ++ M v).getD i 0 = (M v).getD (i-len) 0 := by
      rw [List.getD_append_right _ _ _ _ (by rw [hlen]; omega), hlen]
    simp only [he]; exact hM (i-len)

theorem ldeg_ofFn {d : Fin 10 → Nat} {m : Nat} (F : (Fin 10 → K) → Fin m → K)
    (hF : ∀ i, VDeg 10 d (fun v => F v i)) : LDeg d (fun v => List.ofFn (F v)) := by
  intro i
  by_cases hi : i < m
  · simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, dif_pos hi, Option.getD_some]
    exact hF ⟨i, hi⟩
  · simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, dif_neg hi, Option.getD_none]
    exact vdeg_const 10 d (0 : K)

theorem ldeg_map_mul {d e : Fin 10 → Nat} (S : (Fin 10 → K) → K)
    (L : (Fin 10 → K) → List K) (hS : VDeg 10 d S) (hL : LDeg e L) :
    LDeg (fun i => d i+e i) (fun v => (L v).map (fun x => S v*x)) := by
  intro i
  have he (v : Fin 10 → K) : ((L v).map (fun x => S v*x)).getD i 0 = S v*(L v).getD i 0 := by
    simpa only [mul_zero] using List.getD_map (l := L v) (d := (0 : K)) (n := i) (fun x => S v*x)
  simp only [he]
  exact vdeg_mul hS (hL i)

#print axioms ldeg_mono
#print axioms ldeg_nil
#print axioms ldeg_cons
#print axioms ldeg_append
#print axioms ldeg_ofFn
#print axioms ldeg_map_mul

theorem vdeg_add_same {n : Nat} {d : Fin n → Nat} {G H : (Fin n → K) → K}
    (hG : VDeg n d G) (hH : VDeg n d H) : VDeg n d (fun v => G v+H v) := by
  simpa only [max_self] using vdeg_add hG hH

#print axioms vdeg_add_same

/-- The reconstruction helper is linear in its ten input limbs. -/
theorem vdeg_valueReconstruct {d : Fin 10 → Nat} (o : (Fin 10 → K) → Fin 16 → K)
    (ho : ∀ i, VDeg 10 d (fun v => o v i)) :
    VDeg 10 d (fun v => valueReconstruct10 (o v)) := by
  simp only [value_reconstruct10_eq]
  have hmul (a : K) (i : Fin 16) := vdeg_smul a (ho i)
  repeat' first
    | exact ho _
    | exact hmul _ _
    | apply vdeg_add_same

#print axioms vdeg_valueReconstruct

theorem vdeg_scheduleNodes :
    VDeg 10 highDeg (fun v : Fin 10 → K => scheduleNodes (selAt v)) := by
  have he (v : Fin 10 → K) : scheduleNodes (selAt v) =
      g2SumHigh (selAt v) 4 21 (by omega) + g2SumHigh (selAt v) 33 24 (by omega) := by
    simp only [scheduleNodes, g2SumHigh, g2_fold_add, List.sum_append, zero_add]
  simp only [he]
  exact vdeg_add_same (vdeg_g2SumHigh _ _ _) (vdeg_g2SumHigh _ _ _)

#print axioms vdeg_scheduleNodes
attribute [local irreducible] scheduleNodes

-- The tactic constructs only applications of the proved degree calculus.
-- The final bound is a separate natural-number inequality.
attribute [local irreducible] openingsOf selAt g2High g2Low g2SumHigh valueReconstruct10

syntax "degree_core" : tactic
macro_rules
| `(tactic| degree_core) => `(tactic|
  first
  | assumption
  | exact vdeg_openings_z _ _
  | exact vdeg_openings_succ _ _
  | exact vdeg_openings_xor12 _ _
  | exact vdeg_honestClaims_zero _ _
  | exact vdeg_selAt _
  | exact vdeg_g2High _
  | exact vdeg_g2Low _
  | exact vdeg_g2SumHigh _ _ _
  | exact vdeg_scheduleNodes
  | (apply vdeg_valueReconstruct; intro i; degree_core)
  | exact vdeg_const _ (fun _ => 0) _
  | (apply vdeg_add; all_goals degree_core)
  | (apply vdeg_sub; all_goals degree_core)
  | (apply vdeg_mul; all_goals degree_core)
  | (apply vdeg_neg; degree_core)
  | (apply vdeg_pow; degree_core))

macro "degree_bound" : tactic => `(tactic|
  (apply vdeg_mono <;> first
    | degree_core
    | (intro c; (try simp only [highDeg, lowDeg]); (try split_ifs) <;> omega)))


/-- The literal value range includes successor bits and has bound twenty. -/
theorem ldeg_valueRange (t : Trace K) :
    LDeg (fun _ => 20) (fun v => valueRange (openingsOf (honestClaims t v))) := by
  unfold valueRange
  apply ldeg_append _ _ 30 (by intro v; simp only [List.length_append, List.length_ofFn])
  · apply ldeg_append _ _ 20 (by intro v; simp only [List.length_append, List.length_ofFn])
    · apply ldeg_append _ _ 10 (by intro v; simp only [List.length_ofFn])
      · apply ldeg_ofFn; intro i; degree_bound
      · apply ldeg_ofFn; intro i; degree_bound
    · apply ldeg_ofFn; intro i; degree_bound
  · apply ldeg_cons
    · degree_bound
    · apply ldeg_cons
      · degree_bound
      · apply ldeg_cons
        · degree_bound
        · exact ldeg_nil _

#print axioms ldeg_valueRange

theorem ldeg_valueFamily (pub : Public K) (t : Trace K) :
    LDeg (fun _ => 26) (fun v => valueFamily.residuals pub (openingsOf (honestClaims t v)) (selAt v)) := by
  simp only [valueFamily, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two]
  apply ldeg_append _ _ 33 (by intro v; simp only [List.length_map, valueRange, List.length_append, List.length_ofFn, List.length_cons, List.length_nil])
  · apply ldeg_mono
    · apply ldeg_map_mul
      · degree_core
      · exact ldeg_valueRange t
    · intro c; norm_num
  · apply ldeg_cons
    · degree_bound
    · apply ldeg_cons
      · degree_bound
      · exact ldeg_nil _

#print axioms ldeg_valueFamily

theorem ldeg_occupancyFamily (pub : Public K) (t : Trace K) :
    LDeg (fun _ => 26) (fun v => occupancyFamily.residuals pub (openingsOf (honestClaims t v)) (selAt v)) := by
  simp only [occupancyFamily, occupancyLanesLiteral]
  apply ldeg_append _ _ 11 (by intro v; simp only [List.length_append, List.length_ofFn, List.length_cons, List.length_nil])
  · apply ldeg_append _ _ 3 (by intro v; simp only [List.length_cons, List.length_nil])
    · apply ldeg_cons
      · degree_bound
      · apply ldeg_cons
        · degree_bound
        · apply ldeg_cons
          · degree_bound
          · exact ldeg_nil _
    · apply ldeg_ofFn; intro i; degree_bound
  · apply ldeg_cons
    · degree_bound
    · exact ldeg_nil _

#print axioms ldeg_occupancyFamily

theorem ldeg_assetFamily (pub : Public K) (t : Trace K) :
    LDeg (fun _ => 26) (fun v => assetFamily.residuals pub (openingsOf (honestClaims t v)) (selAt v)) := by
  cases hv : pub.variant <;> cases ha : pub.withdrawalAmount
  all_goals
    simp only [assetFamily, assetScalarLanes, hv, ha, Option.isSome_none, Option.isSome_some,
      Bool.false_eq_true, ite_false, ite_true, Option.getD_none, Option.getD_some]
    apply ldeg_cons
    · degree_bound
    · apply ldeg_cons
      · degree_bound
      · exact ldeg_nil _

#print axioms ldeg_assetFamily

theorem ldeg_scheduleFamily (pub : Public K) (t : Trace K) :
    LDeg (fun _ => 26) (fun v => scheduleFamily.residuals pub (openingsOf (honestClaims t v)) (selAt v)) := by
  simp only [scheduleFamily]
  apply ldeg_append _ _ 16 (by intro v; simp only [List.length_ofFn])
  · apply ldeg_ofFn; intro lane
    cases hv : pub.variant <;>
      simp only [scheduleInitial, scheduleVariantSelectors] <;>
      split_ifs <;> degree_bound
  · apply ldeg_ofFn; intro lane
    cases hv : pub.variant <;>
      simp only [scheduleAbsorption, scheduleAbsorptionLiteral, scheduleVariantSelectors] <;>
      split_ifs <;> degree_bound

#print axioms ldeg_scheduleFamily

theorem ldeg_pathFamily (pub : Public K) (t : Trace K) :
    LDeg (fun _ => 26) (fun v => pathFamily.residuals pub (openingsOf (honestClaims t v)) (selAt v)) := by
  simp only [pathFamily, pathLanes, pathSelector]
  apply ldeg_append _ _ 9 (by intro v; simp only [List.length_append, List.length_cons, List.length_nil, List.length_ofFn])
  · apply ldeg_append _ _ 1 (by intro v; simp only [List.length_cons, List.length_nil])
    · apply ldeg_cons
      · degree_bound
      · exact ldeg_nil _
    · apply ldeg_ofFn; intro i; degree_bound
  · apply ldeg_ofFn; intro i; degree_bound

#print axioms ldeg_pathFamily

/-- A symbolic accumulator rule; its list may be a generated descriptor table. -/
theorem pointwise_foldl {V A I : Type} (P : (V → A) → Prop) (xs : List I)
    (step : V → A → I → A) (a : V → A) (ha : P a)
    (hs : ∀ b, P b → ∀ i, P (fun v => step v (b v) i)) :
    P (fun v => xs.foldl (step v) (a v)) := by
  induction xs generalizing a with
  | nil => exact ha
  | cons i xs ih => exact ih _ (hs a ha i)

#print axioms pointwise_foldl

attribute [local irreducible] digestKeys digestTarget

theorem vdeg_publicDigestLanes (pub : Public K) (t : Trace K) :
    ∀ lane, VDeg 10 (fun _ => 26)
      (fun v => publicDigestLanes pub (openingsOf (honestClaims t v)) (selAt v) lane) := by
  unfold publicDigestLanes
  apply pointwise_foldl (fun b : (Fin 10 → K) → Digest K =>
    ∀ lane, VDeg 10 (fun _ => 26) (fun v => b v lane))
  · intro lane; exact vdeg_const _ _ _
  · intro a ha key lane
    simp only [digestAddBinding]
    have hai := ha lane
    degree_bound

#print axioms vdeg_publicDigestLanes

theorem ldeg_digestFamily (pub : Public K) (t : Trace K) :
    LDeg (fun _ => 26) (fun v => digestFamily.residuals pub (openingsOf (honestClaims t v)) (selAt v)) := by
  unfold digestFamily
  exact ldeg_ofFn _ (vdeg_publicDigestLanes pub t)

#print axioms ldeg_digestFamily

attribute [local irreducible] copyActiveRowMasks copyPatterns copyLinks copyPowers copyLinkWeight

theorem vdeg_copySelectorMaskSum16 {d : Fin 10 → Nat}
    (values : (Fin 10 → K) → Fin 16 → K)
    (hv : ∀ i, VDeg 10 d (fun v => values v i)) (mask : Nat) :
    VDeg 10 d (fun v => copySelectorMaskSum16 (values v) mask) := by
  unfold copySelectorMaskSum16
  dsimp only
  split_ifs
  all_goals
    apply pointwise_foldl (VDeg 10 d)
    · exact vdeg_const _ _ _
    · intro a ha i
      have hi := hv i
      degree_bound

#print axioms vdeg_copySelectorMaskSum16
attribute [local irreducible] copySelectorMaskSum16

theorem vdeg_copySelectorRow (r : Fin 1024) :
    VDeg 10 (fun _ => 1) (fun v : Fin 10 → K => copySelectorRow (copySelectors (selAt v)) r) := by
  unfold copySelectorRow copySelectors
  degree_bound

#print axioms vdeg_copySelectorRow

theorem vdeg_copyActiveLiteral :
    VDeg 10 (fun _ => 1) (fun v : Fin 10 → K => copyActiveLiteral (copySelectors (selAt v))) := by
  unfold copyActiveLiteral
  apply pointwise_foldl (VDeg 10 (fun _ => 1))
  · exact vdeg_const _ _ _
  · intro a ha block
    dsimp only
    split_ifs
    · have hm := vdeg_copySelectorMaskSum16 (fun v : Fin 10 → K => g2Low (selAt v))
        (fun i => vdeg_g2Low i) (copyActiveRowMasks block)
      change VDeg 10 _ (fun v => a v + g2High (selAt v) block *
        copySelectorMaskSum16 (g2Low (selAt v)) (copyActiveRowMasks block))
      degree_bound
    · exact ha

#print axioms vdeg_copyActiveLiteral

theorem vdeg_activeAt : VDeg 10 (fun _ => 1) (fun v : Fin 10 → K => activeAt v) :=
  vdeg_copyActiveLiteral

#print axioms vdeg_activeAt

attribute [local irreducible] copyActiveLiteral copySelectorRow

theorem vdeg_copyPatternValues (t : Trace K) (lam : K) (p : Fin 14) :
    VDeg 10 (fun _ => 1) (fun v => copyPatternValuesLiteral (openingsOf (honestClaims t v)).z lam p) := by
  simp only [copy_pattern_values_eq, copyPatternTuple]
  apply vdeg_sum
  intro i _
  split_ifs <;> degree_bound

#print axioms vdeg_copyPatternValues
attribute [local irreducible] copyPatternValuesLiteral

theorem vdeg_copyAccumulateEndpoint (t : Trace K) (lam : K)
    (values weights : (Fin 10 → K) → Fin 2 → K)
    (hv : ∀ i, VDeg 10 (fun _ => 2) (fun v => values v i))
    (hw : ∀ i, VDeg 10 (fun _ => 2) (fun v => weights v i))
    (ep : CopyEndpoint) (tag : Nat) (weight : K) :
    (∀ i, VDeg 10 (fun _ => 2) (fun v =>
      (copyAccumulateEndpoint (values v) (weights v) ep tag weight
        (copyPatternValuesLiteral (openingsOf (honestClaims t v)).z lam)
        (copySelectors (selAt v))).1 i)) ∧
    (∀ i, VDeg 10 (fun _ => 2) (fun v =>
      (copyAccumulateEndpoint (values v) (weights v) ep tag weight
        (copyPatternValuesLiteral (openingsOf (honestClaims t v)).z lam)
        (copySelectors (selAt v))).2 i)) := by
  have hs := vdeg_copySelectorRow (K := K) ep.row
  have hp := vdeg_copyPatternValues t lam ep.pattern
  constructor <;> intro i
  all_goals
    have hv0 := hv ep.slot
    have hv1 := hv i
    have hw0 := hw ep.slot
    have hw1 := hw i
    simp only [copyAccumulateEndpoint, Function.update_apply]
    split_ifs <;> degree_bound

#print axioms vdeg_copyAccumulateEndpoint

/-- A uniform quadratic invariant for all four endpoint accumulators. -/
def CopyDeg (r : (Fin 10 → K) → CopyRowExtension K) : Prop :=
  (∀ i, VDeg 10 (fun _ => 2) (fun v => (r v).producerValues i)) ∧
  (∀ i, VDeg 10 (fun _ => 2) (fun v => (r v).producerWeights i)) ∧
  (∀ i, VDeg 10 (fun _ => 2) (fun v => (r v).consumerValues i)) ∧
  (∀ i, VDeg 10 (fun _ => 2) (fun v => (r v).consumerWeights i))

theorem copyDeg_step (pub : Public K) (t : Trace K) (lam : K)
    (r : (Fin 10 → K) → CopyRowExtension K) (hr : CopyDeg r) (link : CopyLink) :
    CopyDeg (fun v => copyAccumulateRow pub
      (copyPatternValuesLiteral (openingsOf (honestClaims t v)).z lam)
      (copySelectors (selAt v)) (r v) link) := by
  have hp := vdeg_copyAccumulateEndpoint t lam _ _ hr.1 hr.2.1
    link.producer link.tag (copyLinkWeight link pub.nextPairIndex pub.variant)
  have hc := vdeg_copyAccumulateEndpoint t lam _ _ hr.2.2.1 hr.2.2.2
    link.consumer link.tag (copyLinkWeight link pub.nextPairIndex pub.variant)
  exact ⟨hp.1, hp.2, hc.1, hc.2⟩

#print axioms copyDeg_step

theorem copyDeg_fold (pub : Public K) (t : Trace K) (lam : K) (links : List CopyLink) :
    CopyDeg (fun v => links.foldl (copyAccumulateRow pub
      (copyPatternValuesLiteral (openingsOf (honestClaims t v)).z lam)
      (copySelectors (selAt v))) ⟨fun _ => 0, fun _ => 0, fun _ => 0, fun _ => 0⟩) := by
  apply pointwise_foldl CopyDeg
  · exact ⟨fun _ => vdeg_const _ _ _, fun _ => vdeg_const _ _ _,
      fun _ => vdeg_const _ _ _, fun _ => vdeg_const _ _ _⟩
  · exact copyDeg_step pub t lam

#print axioms copyDeg_fold

theorem vdeg_copyResidual (r : (Fin 10 → K) → CopyRowExtension K) (hr : CopyDeg r)
    (h : (Fin 10 → K) → K) (hh : VDeg 10 (fun _ => 1) h) (chi : K) :
    VDeg 10 (fun _ => 9) (fun v => copyResidual (r v) (h v) chi) := by
  have hp0 := hr.1 0
  have hp1 := hr.1 1
  have hpw0 := hr.2.1 0
  have hpw1 := hr.2.1 1
  have hc0 := hr.2.2.1 0
  have hc1 := hr.2.2.1 1
  have hcw0 := hr.2.2.2 0
  have hcw1 := hr.2.2.2 1
  simp only [copyResidual, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three]
  degree_bound

#print axioms vdeg_copyResidual

theorem vdeg_copyEvaluate (pub : Public K) (t : Trace K) (lam chi : K) :
    VDeg 10 (fun _ => 10) (fun v =>
      (copyEvaluateWithSelectors (openingsOf (honestClaims t v)).z (honestClaims t v 0 26)
        (copySelectors (selAt v)) lam chi pub.nextPairIndex pub.variant).1) := by
  have hr := copyDeg_fold pub t lam copyLinks
  have hres := vdeg_copyResidual _ hr _ (vdeg_honestClaims_zero t 26) chi
  simp only [copyEvaluateWithSelectors]
  exact vdeg_mul vdeg_copyActiveLiteral hres

#print axioms vdeg_copyEvaluate

theorem ldeg_copyFamily (pub : Public K) (t : Trace K) (lam chi : K) :
    LDeg (fun _ => 26) (fun v => copyFamily.residuals pub lam chi
      (openingsOf (honestClaims t v)) (honestClaims t v 0 26) (selAt v)) := by
  unfold copyFamily
  apply ldeg_cons
  · exact vdeg_mono (vdeg_copyEvaluate pub t lam chi) (fun _ => by omega)
  · exact ldeg_nil _

#print axioms ldeg_copyFamily

-- The four-output linear map is handled algebraically; no round table or
-- permutation is evaluated.
attribute [local irreducible] poseidonExternalInitial poseidonExternalFinal
  poseidonInternalConstants poseidonInternalShifts poseidonPermutation

theorem vdeg_poseidonMat4 {d : Fin 10 → Nat}
    (o : (Fin 10 → K) → Fin 4 → K) (ho : ∀ i, VDeg 10 d (fun v => o v i))
    (lane : Fin 4) : VDeg 10 d (fun v => poseidonMat4 (o v) lane) := by
  fin_cases lane <;> simp only [poseidonMat4]
  all_goals
    repeat' first | exact ho _ | apply vdeg_add_same

#print axioms vdeg_poseidonMat4
attribute [local irreducible] poseidonMat4

theorem vdeg_poseidonExternalLinear {d : Fin 10 → Nat}
    (o : (Fin 10 → K) → Fin 16 → K) (ho : ∀ i, VDeg 10 d (fun v => o v i))
    (lane : Fin 16) : VDeg 10 d (fun v => poseidonExternalLinear (o v) lane) := by
  have hl (g c : Fin 4) : VDeg 10 d (fun v => poseidonMat4
      (fun i => o v ⟨4*g.val+i.val, by omega⟩) c) :=
    vdeg_poseidonMat4 _ (fun i => ho _) c
  simp only [poseidonExternalLinear]
  apply vdeg_add_same
  · exact hl ⟨lane.val / 4, by omega⟩ ⟨lane.val % 4, by omega⟩
  · repeat' first | exact hl _ _ | exact vdeg_const 10 d (0 : K) | apply vdeg_add_same

#print axioms vdeg_poseidonExternalLinear
attribute [local irreducible] poseidonExternalLinear

theorem vdeg_poseidonInternalLinear {d : Fin 10 → Nat}
    (o : (Fin 10 → K) → Fin 16 → K) (ho : ∀ i, VDeg 10 d (fun v => o v i))
    (lane : Fin 16) : VDeg 10 d (fun v => poseidonInternalLinear (o v) lane) := by
  have hs : VDeg 10 d (fun v =>
      (List.ofFn (fun i : Fin 15 => o v i.succ)).foldl (· + ·) 0) := by
    simp only [g2_fold_add, List.sum_ofFn, zero_add]
    exact vdeg_sum _ _ (fun i _ => ho i.succ)
  have h0 := ho 0
  have hi := ho lane
  simp only [poseidonInternalLinear]
  split_ifs <;> degree_bound

#print axioms vdeg_poseidonInternalLinear
attribute [local irreducible] poseidonInternalLinear

theorem vdeg_poseidonFullRound {d : Fin 10 → Nat}
    (o cs : (Fin 10 → K) → Fin 16 → K)
    (ho : ∀ i, VDeg 10 d (fun v => o v i))
    (hc : ∀ i, VDeg 10 d (fun v => cs v i)) (lane : Fin 16) :
    VDeg 10 (fun c => 5*d c) (fun v => poseidonFullRound (o v) (cs v) lane) := by
  unfold poseidonFullRound
  apply vdeg_poseidonExternalLinear
  intro i
  simpa only [poseidon_pow5_eq] using vdeg_pow (vdeg_add_same (ho i) (hc i)) 5

#print axioms vdeg_poseidonFullRound
attribute [local irreducible] poseidonFullRound

theorem vdeg_poseidonInternalRound {d : Fin 10 → Nat}
    (o : (Fin 10 → K) → Fin 16 → K) (cs : (Fin 10 → K) → K)
    (ho : ∀ i, VDeg 10 d (fun v => o v i)) (hc : VDeg 10 d cs) (lane : Fin 16) :
    VDeg 10 (fun c => 5*d c) (fun v => poseidonInternalRound (o v) (cs v) lane) := by
  unfold poseidonInternalRound
  apply vdeg_poseidonInternalLinear
  intro i
  split_ifs
  · simpa only [poseidon_pow5_eq] using vdeg_pow (vdeg_add_same (ho 0) hc) 5
  · exact vdeg_mono (ho i) (fun c => by omega)

#print axioms vdeg_poseidonInternalRound
attribute [local irreducible] poseidonInternalRound

theorem vdeg_poseidonLeadingPair (t : Trace K) (lane : Fin 16) :
    VDeg 10 (fun _ => 25) (fun v => poseidonLeadingPair
      (openingsOf (honestClaims t v)).z (openingsOf (honestClaims t v)).xor12 lane) := by
  simp only [poseidonLeadingPair]
  apply vdeg_poseidonFullRound (d := fun _ => 5)
  · intro i
    apply vdeg_poseidonFullRound (d := fun _ => 1)
    · intro j
      apply vdeg_poseidonExternalLinear
      intro k
      split_ifs <;> degree_bound
    · intro j; exact vdeg_const _ _ _
  · intro i; exact vdeg_const _ _ _

#print axioms vdeg_poseidonLeadingPair
attribute [local irreducible] poseidonLeadingPair

theorem vdeg_poseidonInterpolatedFullPair (t : Trace K) (lane : Fin 16) :
    VDeg 10 (fun _ => 25) (fun v => poseidonInterpolatedFullPair
      (openingsOf (honestClaims t v)).z (g2Low (selAt v)) lane) := by
  simp only [poseidonInterpolatedFullPair]
  apply vdeg_poseidonFullRound (d := fun _ => 5)
  · intro i
    apply vdeg_poseidonFullRound (d := fun _ => 1)
    · exact vdeg_openings_z t
    · intro j; degree_bound
  · intro i; degree_bound

#print axioms vdeg_poseidonInterpolatedFullPair
attribute [local irreducible] poseidonInterpolatedFullPair

theorem vdeg_poseidonInterpolatedInternalPair (t : Trace K) (lane : Fin 16) :
    VDeg 10 (fun _ => 25) (fun v => poseidonInterpolatedInternalPair
      (openingsOf (honestClaims t v)).z (g2Low (selAt v)) lane) := by
  simp only [poseidonInterpolatedInternalPair]
  apply vdeg_poseidonInternalRound (d := fun _ => 5)
  · intro i
    apply vdeg_poseidonInternalRound (d := fun _ => 1)
    · exact vdeg_openings_z t
    · simp only [g2_fold_add, List.sum_ofFn, zero_add]
      apply vdeg_sum; intro j _; degree_bound
  · simp only [g2_fold_add, List.sum_ofFn, zero_add]
    apply vdeg_sum; intro j _; degree_bound

#print axioms vdeg_poseidonInterpolatedInternalPair
attribute [local irreducible] poseidonInterpolatedInternalPair

theorem vdeg_poseidonScalarResidual (t : Trace K) (lane : Fin 16) :
    VDeg 10 (fun _ => 26) (fun v => poseidonScalarResidual (openingsOf (honestClaims t v))
      (g2SumHigh (selAt v) 0 57 (by omega)) (g2Low (selAt v)) lane) := by
  have hl := vdeg_poseidonLeadingPair t lane
  have hf := vdeg_poseidonInterpolatedFullPair t lane
  have hi := vdeg_poseidonInterpolatedInternalPair t lane
  have hfullLow : VDeg 10 lowDeg (fun v : Fin 10 → K =>
      ([1, 9, 10] : List (Fin 16)).foldl (fun s i => s + g2Low (selAt v) i) 0) := by
    apply pointwise_foldl (VDeg 10 lowDeg)
    · exact vdeg_const _ _ _
    · intro a ha i; exact vdeg_add_same ha (vdeg_g2Low i)
  have hintLow : VDeg 10 lowDeg (fun v : Fin 10 → K =>
      (List.ofFn (fun i : Fin 7 => g2Low (selAt v) ⟨i.val+2, by omega⟩)).foldl (· + ·) 0) := by
    simp only [g2_fold_add, List.sum_ofFn, zero_add]
    exact vdeg_sum _ _ (fun i _ => vdeg_g2Low _)
  simp only [poseidonScalarResidual]
  degree_bound

#print axioms vdeg_poseidonScalarResidual

theorem ldeg_poseidonPackedFamily (pub : Public K) (t : Trace K)
    {F : Subfield K} (B : PackBasis F) :
    LDeg (fun _ => 26) (fun v => (poseidonPackedFamily B).residuals pub
      (openingsOf (honestClaims t v)) (selAt v)) := by
  unfold poseidonPackedFamily
  apply ldeg_ofFn; intro g
  apply vdeg_pack4; intro i
  exact vdeg_poseidonScalarResidual t _

#print axioms ldeg_poseidonPackedFamily

/-- Every scalar lane follows the literal family dispatch. Positive is not
an additional branch of scalarLaneAt. -/
theorem vdeg_scalarLaneAt (pub : Public K) (t : Trace K) (i : Nat) :
    VDeg 10 (fun _ => 26) (fun v => scalarLaneAt pub (openingsOf (honestClaims t v)) (selAt v) i) := by
  unfold scalarLaneAt
  split_ifs
  · exact vdeg_add_same (ldeg_scheduleFamily pub t i) (ldeg_occupancyFamily pub t i)
  · exact ldeg_scheduleFamily pub t i
  · exact ldeg_pathFamily pub t (i-32)
  · exact ldeg_valueFamily pub t (i-49)
  · exact ldeg_digestFamily pub t (i-84)
  · exact ldeg_assetFamily pub t (i-92)
  · exact vdeg_const _ _ _

#print axioms vdeg_scalarLaneAt
attribute [local irreducible] scalarLaneAt

/-- The required vector bound, for every one of the 29 production lanes. -/
theorem vdeg_laneAt (pub : Public K) (t : Trace K) (lam chi : K)
    {F : Subfield K} (B : PackBasis F) (i : Fin 29) :
    VDeg 10 (fun _ => 26) (fun v => laneAt pub lam chi B (openingsOf (honestClaims t v))
      (honestClaims t v 0 26) (selAt v) i) := by
  unfold laneAt
  split_ifs
  · exact ldeg_poseidonPackedFamily pub t B i.val
  · apply vdeg_pack4; intro j
    exact vdeg_scalarLaneAt pub t _
  · exact ldeg_copyFamily pub t lam chi 0

#print axioms vdeg_laneAt
end R0P.SemDegree
end
