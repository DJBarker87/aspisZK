import R0P.SemHonest
import R0Z.HelperInvariant

/-! T2b-1: Boolean-row invariance under eligible C1 noise, and the exact
zero-sum H1-padding correction. All row sums and registries stay symbolic. -/
set_option autoImplicit false
noncomputable section
namespace R0Z.TerminalEligible
open R0P R0P.SemSource R0P.Sumcheck R0Z.MaskLayout R0Z.HonestView
attribute [local instance] Classical.propDecidable
attribute [local irreducible] copyLinks copyPatterns copyActiveRowMasks copyInactiveRows
variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K] {F : Subfield K}

/-- A protected semantic cell survives both noise and balancing. -/
theorem cell_eligible (t : Trace K) (e : EligibleNoise K F) (c : Fin 29) (r : Fin 1024)
    (hr : r ≠ 1023) (he : ¬ eligible c r) : applyEligible t e c r = t c r := by
  unfold applyEligible
  split_ifs with hc
  · simp only [balance, if_neg hr, semanticNoise, dif_neg he, add_zero]
  · rfl

theorem cell_low (t : Trace K) (e : EligibleNoise K F) (c : Fin 29) (r : Fin 1024)
    (hr : r.val < 912) (hl : r.val % 16 < 13) : applyEligible t e c r = t c r := by
  apply cell_eligible t e c r
  · intro h; subst r; norm_num at hr
  · unfold eligible
    omega

/-! ### Reads protected by the per-family selectors -/

theorem schedule_eligible (pub : Public K) (t : Trace K) (e : EligibleNoise K F)
    (r : Fin 1024) : scheduleFamily.residuals pub (rowOpenings (applyEligible t e) r) (rowSel r) =
      scheduleFamily.residuals pub (rowOpenings t r) (rowSel r) := by
  unfold scheduleFamily
  apply congrArg₂ List.append <;> apply congrArg List.ofFn <;> funext c
  · rw [schedule_initial_row, schedule_initial_row]
    split_ifs with hl hf hn
    · rw [cell_low t e _ r (by unfold ScheduleFull at hf; omega) (by omega)]
    · rw [cell_low t e _ r (by unfold ScheduleNode at hn; omega) (by omega)]
    · rfl
    · rfl
  · rw [schedule_absorption_row, schedule_absorption_row]
    split_ifs with ha
    · apply cell_low t e _ r
      · have hb : r.val / 16 < 57 := by
          have hh := ha.2
          unfold ScheduleAbsorbs at hh
          split_ifs at hh <;> omega
        omega
      · omega
    · rfl

theorem digest_row_low (pub : Public K) (key : DigestKey) :
    (digestRow pub key).val < 912 ∧ (digestRow pub key).val % 16 < 13 := by
  have hc := digest_carry_le pub.nextPairIndex
  cases key <;> simp only [digestRow, g2Row, Fin.val_mk]
  all_goals first | omega | (split_ifs <;> (try dsimp only) <;> omega)

theorem digest_eligible (pub : Public K) (t : Trace K) (e : EligibleNoise K F)
    (r : Fin 1024) : digestFamily.residuals pub (rowOpenings (applyEligible t e) r) (rowSel r) =
      digestFamily.residuals pub (rowOpenings t r) (rowSel r) := by
  unfold digestFamily
  apply congrArg List.ofFn
  funext lane
  simp only [publicDigestLanes, digest_fold_eq]
  congr 1
  apply congrArg List.sum
  apply List.map_congr_left
  intro key _
  by_cases hr : digestRow pub key = r
  · subst r
    simp only [rowOpenings]
    rw [cell_low t e _ _ (digest_row_low pub key).1 (digest_row_low pub key).2]
  · rw [rowSel_ne r _ hr, zero_mul, zero_mul]

/-- The forest path support supplies a literal `forestPathUsed` witness. -/
theorem forest_used (r : Fin 1024) (hr : PathRow r) (c : Fin 29)
    (hc : c.val ≤ 8) : forestPathUsed c.val r.val := by
  rcases hr with ⟨hh, hb, hl⟩
  rcases hl with hl | hl | hl | hl
  all_goals
    refine ⟨⟨4 * (r.val / 16 - 57) + (r.val % 16 - 1) / 4, by omega⟩, ?_⟩
    dsimp only
    left
    constructor <;> omega

theorem forest_succ_used (r : Fin 1024) (hr : PathRow r) (c : Fin 29) :
    forestPathUsed c.val (succRow r).val := by
  rcases hr with ⟨hh, hb, hl⟩
  rcases hl with hl | hl | hl | hl
  all_goals
    refine ⟨⟨4 * (r.val / 16 - 57) + (r.val % 16 - 1) / 4, by omega⟩, ?_⟩
    dsimp only [succRow]
    right
    omega

theorem cell_forest (t : Trace K) (e : EligibleNoise K F) (c : Fin 29) (r : Fin 1024)
    (hr : 912 ≤ r.val ∧ r.val < 1008) (hu : forestPathUsed c.val r.val) :
    applyEligible t e c r = t c r := by
  apply cell_eligible t e c r
  · intro h; subst r; norm_num at hr
  · simp only [eligible, if_pos hr.2, hu, not_true_eq_false, and_false, or_false]
    omega

theorem path_eligible (pub : Public K) (t : Trace K) (e : EligibleNoise K F)
    (r : Fin 1024) : pathFamily.residuals pub (rowOpenings (applyEligible t e) r) (rowSel r) =
      pathFamily.residuals pub (rowOpenings t r) (rowSel r) := by
  simp only [pathFamily, path_selector_row]
  by_cases hr : PathRow r
  · have hz (c : Fin 16) (hc : c.val ≤ 8) :
        (rowOpenings (applyEligible t e) r).z c = (rowOpenings t r).z c := by
      apply cell_forest
      · unfold PathRow at hr; omega
      · exact forest_used r hr _ hc
    have hs : (rowOpenings (applyEligible t e) r).succ = (rowOpenings t r).succ := by
      funext c
      apply cell_forest
      · unfold PathRow succRow at *; dsimp only; omega
      · exact forest_succ_used r hr _
    have h0 := hz 0 (by norm_num)
    have hi (i : Fin 8) := hz (i.addNat 1 |>.castLE (by omega)) (by simp only [Fin.val_castLE, Fin.val_addNat]; omega)
    simp only [pathLanes, h0, hs, hi]
  · simp only [if_neg hr, pathLanes, zero_mul]

/-- Congruence of a fold uses only entries actually in its list. -/
private theorem fold_congr {I V : Type} (xs : List I) (f g : V → I → V)
    (h : ∀ i ∈ xs, ∀ v, f v i = g v i) (v : V) : xs.foldl f v = xs.foldl g v := by
  induction xs generalizing v with
  | nil => rfl
  | cons i xs ih =>
    simp only [List.foldl_cons]
    rw [h i List.mem_cons_self v]
    exact ih (fun j hj => h j (List.mem_cons_of_mem i hj)) _

private theorem selector_row (b r : Fin 1024) :
    copySelectorRow (copySelectors (rowSel (K := K) b)) r = rowSel b r := by
  simp only [copySelectorRow, copySelectors, g2_high_row, g2_low_row, rowSel]
  by_cases hr : r = b
  · subst r; simp
  · have hp : ¬ (r.val / 16 = b.val / 16 ∧ r.val % 16 = b.val % 16) := by
      intro h; apply hr; apply Fin.ext; omega
    by_cases hh : r.val / 16 = b.val / 16
    · have hl : r.val % 16 ≠ b.val % 16 := fun h => hp ⟨hh,h⟩
      simp only [if_pos hh, if_neg hl, if_neg hr, mul_zero]
    · simp only [if_neg hh, if_neg hr, zero_mul]

theorem copy_endpoint_eligible (t : Trace K) (e : EligibleNoise K F) (lam : K)
    (r : Fin 1024) (ep : CopyEndpoint) (hp : HelperInvariant.Protected ep)
    (values weights : Fin 2 → K) (tag : Nat) (weight : K) :
    copyAccumulateEndpoint values weights ep tag weight
      (copyPatternValuesLiteral (rowOpenings (applyEligible t e) r).z lam) (copySelectors (rowSel r)) =
    copyAccumulateEndpoint values weights ep tag weight
      (copyPatternValuesLiteral (rowOpenings t r).z lam) (copySelectors (rowSel r)) := by
  unfold copyAccumulateEndpoint
  rw [selector_row]
  by_cases hr : ep.row = r
  · subst r
    have he : copyPatternValuesLiteral (rowOpenings (applyEligible t e) ep.row).z lam ep.pattern =
        copyPatternValuesLiteral (rowOpenings t ep.row).z lam ep.pattern := by
      unfold copyPatternValuesLiteral
      apply fold_congr
      intro i _ v
      by_cases hi : (copyPatterns ep.pattern).kinds i = 1
      · simp only [if_pos hi, rowOpenings, HelperInvariant.protected_cell t e ep hp i hi]
      · simp only [if_neg hi]
    rw [he]
  · rw [rowSel_ne _ _ hr]
    simp only [zero_mul]

/-- Copy includes every LogUp and positivity endpoint in the protected registry. -/
theorem copy_eligible (pub : Public K) (t : Trace K) (e : EligibleNoise K F)
    (lam chi : K) (r : Fin 1024) :
    copyFamily.residuals pub lam chi (rowOpenings (applyEligible t e) r)
      (applyEligible t e 26 r) (rowSel r) =
    copyFamily.residuals pub lam chi (rowOpenings t r) (t 26 r) (rowSel r) := by
  have he (row : CopyRowExtension K) (link : CopyLink) (hl : link ∈ copyLinks) :
      copyAccumulateRow pub (copyPatternValuesLiteral (rowOpenings (applyEligible t e) r).z lam)
        (copySelectors (rowSel r)) row link =
      copyAccumulateRow pub (copyPatternValuesLiteral (rowOpenings t r).z lam)
        (copySelectors (rowSel r)) row link := by
    dsimp only [copyAccumulateRow]
    rw [copy_endpoint_eligible t e lam r link.producer (HelperInvariant.protected_registry link hl).1,
      copy_endpoint_eligible t e lam r link.consumer (HelperInvariant.protected_registry link hl).2]
  have hf := fold_congr copyLinks
    (copyAccumulateRow pub (copyPatternValuesLiteral (rowOpenings (applyEligible t e) r).z lam)
      (copySelectors (rowSel r)))
    (copyAccumulateRow pub (copyPatternValuesLiteral (rowOpenings t r).z lam) (copySelectors (rowSel r)))
    (fun link hl row => he row link hl) ⟨fun _ => 0, fun _ => 0, fun _ => 0, fun _ => 0⟩
  unfold copyFamily copyEvaluateWithSelectors
  change [copyActiveLiteral (copySelectors (rowSel r)) * copyResidual
    (copyLinks.foldl (copyAccumulateRow pub _ _) _) (t 26 r) chi] =
    [copyActiveLiteral (copySelectors (rowSel r)) * copyResidual
    (copyLinks.foldl (copyAccumulateRow pub _ _) _) (t 26 r) chi]
  rw [hf]

private theorem poseidon_inactive (o : Openings K) (block : K) (r : Fin 1024)
    (hr : 11 ≤ r.val % 16) (lane : Fin 16) :
    poseidonScalarResidual o block (g2Low (rowSel r)) lane = 0 := by
  have h0 : g2Low (rowSel (K := K) r) 0 = 0 := by rw [g2_low_row, if_neg (by omega)]
  have h1 : g2Low (rowSel (K := K) r) 1 = 0 := by rw [g2_low_row, if_neg (by omega)]
  have h9 : g2Low (rowSel (K := K) r) 9 = 0 := by rw [g2_low_row, if_neg (by omega)]
  have h10 : g2Low (rowSel (K := K) r) 10 = 0 := by rw [g2_low_row, if_neg (by omega)]
  have hi : (fun i : Fin 7 => g2Low (rowSel (K := K) r) ⟨i.val + 2, by omega⟩) = fun _ => 0 := by
    funext i
    rw [g2_low_row, if_neg (by dsimp only; omega)]
  simp only [poseidonScalarResidual, h0, h1, h9, h10, hi, g2_fold_add,
    List.sum_ofFn, Finset.sum_const_zero, List.foldl_cons, List.foldl_nil,
    zero_add, zero_mul, add_zero, mul_zero]

theorem poseidon_eligible (pub : Public K) (B : PackBasis F) (t : Trace K)
    (e : EligibleNoise K F) (r : Fin 1024) :
    (poseidonPackedFamily B).residuals pub (rowOpenings (applyEligible t e) r) (rowSel r) =
      (poseidonPackedFamily B).residuals pub (rowOpenings t r) (rowSel r) := by
  have he (lane : Fin 16) :
      poseidonScalarResidual (rowOpenings (applyEligible t e) r) (g2SumHigh (rowSel r) 0 57 (by omega))
        (g2Low (rowSel r)) lane =
      poseidonScalarResidual (rowOpenings t r) (g2SumHigh (rowSel r) 0 57 (by omega))
        (g2Low (rowSel r)) lane := by
    by_cases hb : r.val / 16 < 57
    · by_cases hl : r.val % 16 < 11
      · have hz : (rowOpenings (applyEligible t e) r).z = (rowOpenings t r).z := by
          funext c
          exact cell_low t e _ r (by omega) (by omega)
        have hs : (rowOpenings (applyEligible t e) r).succ = (rowOpenings t r).succ := by
          funext c
          apply cell_low
          · dsimp only [succRow]; omega
          · dsimp only [succRow]; omega
        unfold poseidonScalarResidual
        rw [hz, hs]
        by_cases h0 : r.val % 16 = 0
        · have hdiv : (xor12Row r).val / 16 = r.val / 16 := by
            change (r.val ^^^ 12) / 2^4 = r.val / 16
            rw [Nat.xor_div_two_pow]
            simp
          have hmod : (xor12Row r).val % 16 = 12 := by
            change (r.val ^^^ 12) % 2^4 = 12
            rw [Nat.xor_mod_two_pow]
            simp only [show 2^4 = (16 : Nat) from rfl, h0]
            rfl
          have hx : (rowOpenings (applyEligible t e) r).xor12 = (rowOpenings t r).xor12 := by
            funext c
            exact cell_low t e _ _ (by omega) (by omega)
          rw [hx]
        · have hz0 : g2Low (rowSel (K := K) r) 0 = 0 := by rw [g2_low_row, if_neg (by omega)]
          rw [hz0]
          simp only [zero_mul]
      · rw [poseidon_inactive _ _ r (by omega), poseidon_inactive _ _ r (by omega)]
    · rw [g2_sum_high_row, if_neg (by omega)]
      simp only [poseidonScalarResidual, zero_mul]
  simp only [poseidonPackedFamily, he]

/-- The translated auxiliary region is protected precisely where the literal
`pairAuxUsed` predicate says it is used. -/
theorem cell_aux (t : Trace K) (e : EligibleNoise K F) (c : Fin 29) (r : Fin 1024)
    (hr : 1008 ≤ r.val ∧ r.val < 1023) (hu : pairAuxUsed c.val (r.val - 48)) :
    applyEligible t e c r = t c r := by
  apply cell_eligible t e c r
  · intro h; subst r; norm_num at hr
  · simp only [eligible, if_neg (by omega : ¬r.val < 1008), hu,
      not_true_eq_false, and_false, or_false]
    omega

/-- Three value records: current, successor and xor12, columns 0 through 10. -/
theorem cell_value (t : Trace K) (e : EligibleNoise K F) (c : Fin 29) (r : Fin 1024)
    (v : Fin 3) (hc : c.val ≤ 10)
    (hr : r.val = 1008 + 2*v.val ∨ r.val = 1009 + 2*v.val ∨ r.val = (1008 + 2*v.val) ^^^ 12) :
    applyEligible t e c r = t c r := by
  have hx0 : (1008 : Nat) ^^^ 12 = 1020 := rfl
  have hx1 : (1010 : Nat) ^^^ 12 = 1022 := rfl
  have hx2 : (1012 : Nat) ^^^ 12 = 1016 := rfl
  have hy0 : (960 : Nat) ^^^ 12 = 972 := rfl
  have hy1 : (962 : Nat) ^^^ 12 = 974 := rfl
  have hy2 : (964 : Nat) ^^^ 12 = 968 := rfl
  have ht : 1008 ≤ r.val ∧ r.val < 1023 := by
    fin_cases v <;> norm_num only [Fin.val_zero, Fin.val_one, Fin.val_ofNat, hx0, hx1, hx2] at hr <;> omega
  apply cell_aux t e c r ht
  refine ⟨by omega, by omega, by omega, Or.inr (Or.inl ⟨v, ?_, hc⟩)⟩
  fin_cases v <;> norm_num only [Fin.val_zero, Fin.val_one, Fin.val_ofNat, hx0, hx1, hx2, hy0, hy1, hy2] at hr ⊢ <;> omega

/-- Conservation and occupancy read exactly these auxiliary cells. -/
theorem cell_aux_tail (t : Trace K) (e : EligibleNoise K F) (c : Fin 29) (r : Fin 1024)
    (hr : (r.val = 1014 ∧ c.val < 3) ∨ (r.val = 1015 ∧ c.val < 2) ∨
      (r.val = 1017 ∧ c.val ≤ 10) ∨ (r.val = 1018 ∧ c.val < 10)) :
    applyEligible t e c r = t c r := by
  apply cell_aux t e c r (by omega)
  refine ⟨by omega, by omega, by omega, Or.inr (Or.inr ?_)⟩
  omega

private theorem valueRange_congr (o p : Openings K)
    (hz : ∀ c : Fin 16, c.val ≤ 10 → o.z c = p.z c)
    (hs : ∀ c : Fin 16, c.val ≤ 10 → o.succ c = p.succ c)
    (hx : ∀ c : Fin 16, c.val ≤ 10 → o.xor12 c = p.xor12 c) : valueRange o = valueRange p := by
  have he (u v : Fin 16 → K) (h : ∀ c : Fin 16, c.val ≤ 10 → u c = v c) :
      valueReconstruct10 u = valueReconstruct10 v := by
    simp only [valueReconstruct10, h 0 (by norm_num), h 1 (by norm_num), h 2 (by norm_num),
      h 3 (by norm_num), h 4 (by norm_num), h 5 (by norm_num), h 6 (by norm_num),
      h 7 (by norm_num), h 8 (by norm_num), h 9 (by norm_num)]
  have hz' (i : Fin 10) := hz (i.castAdd 6) (by simp only [Fin.val_castAdd]; omega)
  have hs' (i : Fin 10) := hs (i.castAdd 6) (by simp only [Fin.val_castAdd]; omega)
  have hx' (i : Fin 10) := hx (i.castAdd 6) (by simp only [Fin.val_castAdd]; omega)
  simp only [valueRange, hz', hs', hx', he _ _ hz, he _ _ hs, he _ _ hx,
    hz 10 (by norm_num), hs 10 (by norm_num), hx 10 (by norm_num)]

theorem value_eligible (pub : Public K) (t : Trace K) (e : EligibleNoise K F)
    (r : Fin 1024) : valueFamily.residuals pub (rowOpenings (applyEligible t e) r) (rowSel r) =
      valueFamily.residuals pub (rowOpenings t r) (rowSel r) := by
  have hv (v : Fin 3) (hr : r.val = 1008 + 2*v.val) :
      valueRange (rowOpenings (applyEligible t e) r) = valueRange (rowOpenings t r) := by
    apply valueRange_congr
    · intro c hc
      exact cell_value t e _ r v hc (Or.inl hr)
    · intro c hc
      apply cell_value t e _ (succRow r) v hc
      right; left
      dsimp only [succRow]
      omega
    · intro c hc
      apply cell_value t e _ (xor12Row r) v hc
      right; right
      dsimp only [xor12Row]
      rw [hr]
  change (valueRange (rowOpenings (applyEligible t e) r)).map
      (fun x => (((0 + rowSel r 1008) + rowSel r 1010) + rowSel r 1012) * x) ++
      [rowSel r 1014 * ((applyEligible t e 0 r - applyEligible t e 1 r) - applyEligible t e 2 r),
       rowSel r 1014 * (applyEligible t e 0 (succRow r) - applyEligible t e 1 (succRow r))] =
    (valueRange (rowOpenings t r)).map
      (fun x => (((0 + rowSel r 1008) + rowSel r 1010) + rowSel r 1012) * x) ++
      [rowSel r 1014 * ((t 0 r - t 1 r) - t 2 r), rowSel r 1014 * (t 0 (succRow r) - t 1 (succRow r))]
  apply congrArg₂ List.append
  · by_cases hr : r = 1008 ∨ r = 1010 ∨ r = 1012
    · rcases hr with rfl | rfl | rfl
      · rw [hv 0 rfl]
      · rw [hv 1 rfl]
      · rw [hv 2 rfl]
    · have h0 : (1008 : Fin 1024) ≠ r := by tauto
      have h2 : (1010 : Fin 1024) ≠ r := by tauto
      have h4 : (1012 : Fin 1024) ≠ r := by tauto
      simp only [rowSel_ne _ _ h0, rowSel_ne _ _ h2, rowSel_ne _ _ h4, zero_add, zero_mul]
      simp only [valueRange, List.map_append, List.map_ofFn, List.map_cons, List.map_nil,
        Function.comp_def]
  · by_cases hr : (1014 : Fin 1024) = r
    · subst r
      have hz (c : Fin 29) (hc : c.val < 3) : applyEligible t e c 1014 = t c 1014 :=
        cell_aux_tail t e c 1014 (Or.inl ⟨rfl,hc⟩)
      have hs (c : Fin 29) (hc : c.val < 2) : applyEligible t e c 1015 = t c 1015 :=
        cell_aux_tail t e c 1015 (Or.inr (Or.inl ⟨rfl,hc⟩))
      norm_num only [rowOpenings, Fin.castLE, show succRow 1014 = 1015 from rfl,
        hz 0 (by norm_num), hz 1 (by norm_num), hz 2 (by norm_num),
        hs 0 (by norm_num), hs 1 (by norm_num)]
    · simp only [rowSel_ne _ _ hr, zero_mul]

theorem occupancy_eligible (pub : Public K) (t : Trace K) (e : EligibleNoise K F)
    (r : Fin 1024) : occupancyFamily.residuals pub (rowOpenings (applyEligible t e) r) (rowSel r) =
      occupancyFamily.residuals pub (rowOpenings t r) (rowSel r) := by
  change occupancyLanesLiteral (rowSel r 1017) (rowSel r 1018) (occupancyExpected pub.variant)
      (rowOpenings (applyEligible t e) r).z =
    occupancyLanesLiteral (rowSel r 1017) (rowSel r 1018) (occupancyExpected pub.variant) (rowOpenings t r).z
  by_cases hi : (1017 : Fin 1024) = r
  · subst r
    have hc (c : Fin 16) (h : c.val ≤ 10) :
        (rowOpenings (applyEligible t e) 1017).z c = (rowOpenings t 1017).z c :=
      cell_aux_tail t e _ 1017 (Or.inr (Or.inr (Or.inl ⟨rfl,h⟩)))
    have hl (i : Fin 8) := hc ⟨2+i.val, by omega⟩ (by dsimp only; omega)
    simp only [occupancyLanesLiteral,
      hc 0 (by norm_num), hc 1 (by norm_num), hc 9 (by norm_num), hc 10 (by norm_num), hl]
  · by_cases ho : (1018 : Fin 1024) = r
    · subst r
      have hc (c : Fin 16) (h : c.val < 10) :
          (rowOpenings (applyEligible t e) 1018).z c = (rowOpenings t 1018).z c :=
        cell_aux_tail t e _ 1018 (Or.inr (Or.inr (Or.inr ⟨rfl,h⟩)))
      have hl (i : Fin 8) := hc ⟨2+i.val, by omega⟩ (by dsimp only; omega)
      simp only [occupancyLanesLiteral, rowSel_ne _ _ hi, zero_mul,
        hc 0 (by norm_num), hc 1 (by norm_num), hc 9 (by norm_num), hl]
    · simp only [occupancyLanesLiteral, rowSel_ne _ _ hi, rowSel_ne _ _ ho, zero_add, zero_mul]

private theorem selected_difference (t : Trace K) (e : EligibleNoise K F) (c : Fin 29)
    (k r : Fin 1024) (v : K) (hk : applyEligible t e c k = t c k) :
    rowSel r k * (applyEligible t e c r - v) = rowSel r k * (t c r - v) := by
  by_cases hr : k = r
  · subst r; rw [hk]
  · rw [rowSel_ne _ _ hr, zero_mul, zero_mul]

theorem asset_eligible (pub : Public K) (t : Trace K) (e : EligibleNoise K F)
    (r : Fin 1024) : assetFamily.residuals pub (rowOpenings (applyEligible t e) r) (rowSel r) =
      assetFamily.residuals pub (rowOpenings t r) (rowSel r) := by
  have h44 := selected_difference t e 1 44 r pub.assetId (cell_low t e 1 44 (by norm_num) (by norm_num))
  have h508 := selected_difference t e 1 508 r pub.assetId (cell_low t e 1 508 (by norm_num) (by norm_num))
  have h460 := selected_difference t e 1 460 r pub.assetId (cell_low t e 1 460 (by norm_num) (by norm_num))
  have h1010 := selected_difference t e 10 1010 r (pub.withdrawalAmount.getD 0)
    (cell_value t e 10 1010 1 (by norm_num) (Or.inl rfl))
  change assetScalarLanes pub.variant pub.withdrawalAmount.isSome
      (rowSel r 44 * (applyEligible t e 1 r - pub.assetId))
      (rowSel r 508 * (applyEligible t e 1 r - pub.assetId))
      (rowSel r 460 * (applyEligible t e 1 r - pub.assetId))
      (rowSel r 1010 * (applyEligible t e 10 r - pub.withdrawalAmount.getD 0)) =
    assetScalarLanes pub.variant pub.withdrawalAmount.isSome
      (rowSel r 44 * (t 1 r - pub.assetId)) (rowSel r 508 * (t 1 r - pub.assetId))
      (rowSel r 460 * (t 1 r - pub.assetId)) (rowSel r 1010 * (t 10 r - pub.withdrawalAmount.getD 0))
  rw [h44, h508, h460, h1010]

/-- Membership only unfolds the filter, never its row universe. -/
theorem mem_inactive (r : Fin 1024) : r ∈ copyInactiveRows ↔ ¬ CopyActiveRow r := by
  rw [copyInactiveRows, Finset.mem_filter]
  simp only [Finset.mem_univ, true_and]

theorem zero_inactive : ¬ CopyActiveRow 0 := by
  have h0 : copyActiveRowMasks 0 = 6144 := by unfold copyActiveRowMasks; rfl
  change ¬ (copyActiveRowMasks 0).testBit 0 = true
  rw [h0]
  decide

theorem padding_active (B : PackBasis F) (tape : MaskTape K F) (r : Fin 1024)
    (hr : CopyActiveRow r) : h1Padding B tape r = 0 := by
  have hn : r ≠ 0 := fun h => zero_inactive (h ▸ hr)
  simp only [h1Padding, balance, if_neg hn, if_pos hr]

/-- The cancellation is generic in the index type and support set. -/
private theorem sum_balanced {I : Type} [Fintype I] [DecidableEq I]
    (S : Finset I) (d : I) (w : I → K) (hw : ∀ r, r ∉ S → w r = 0) :
    (∑ r, if r = d then -(∑ s ∈ S.erase d, w s) else w r) = 0 := by
  have hs : (∑ r ∈ Finset.univ.erase d, w r) = ∑ r ∈ S.erase d, w r := by
    symm
    apply Finset.sum_subset
    · intro r hr
      exact Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp hr).1, Finset.mem_univ r⟩
    · intro r hr hn
      apply hw r
      intro hm
      exact hn (Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp hr).1, hm⟩)
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ d)]
  rw [if_pos rfl]
  have he : (∑ r ∈ Finset.univ.erase d,
      if r = d then -(∑ s ∈ S.erase d, w s) else w r) =
        ∑ r ∈ Finset.univ.erase d, w r := by
    apply Finset.sum_congr rfl
    intro r hr
    exact if_neg (Finset.mem_erase.mp hr).1
  rw [he, hs, add_neg_cancel]

theorem h1Padding_sum (B : PackBasis F) (tape : MaskTape K F) :
    ∑ r : Fin 1024, h1Padding B tape r = 0 := by
  apply sum_balanced copyInactiveRows 0
    (fun r => if CopyActiveRow r then 0 else extensionRaw B tape 1 r)
  intro r hr
  have ha : CopyActiveRow r := by
    by_contra hn
    exact hr ((mem_inactive r).mpr hn)
  exact if_pos ha

theorem h1Padding_bsumB (B : PackBasis F) (tape : MaskTape K F) :
    bsumB 10 (fun b => h1Padding B tape (rowOf b)) = 0 := by
  rw [bsumB_rowOf, h1Padding_sum]

theorem h1Padding_zero (B : PackBasis F) : h1Padding B (0 : MaskTape K F) = 0 := by
  have he (r : Fin 1024) : extensionRaw B (0 : MaskTape K F) 1 r = 0 := by
    simp only [extensionRaw, pack4, Pi.zero_apply, ZeroMemClass.coe_zero, mul_zero, add_zero]
  funext r
  simp only [h1Padding, he, ite_self, balance, Finset.sum_const_zero, neg_zero,
    Pi.zero_apply, ite_self]

theorem openings_applyAff (B : PackBasis F) (u : Trace K) (tape : AffTape K F)
    (r : Fin 1024) : rowOpenings (applyAff B u tape) r = rowOpenings u r := by
  have hc (c : Fin 16) (s : Fin 1024) :
      applyAff B u tape (Fin.castLE (by omega) c) s = u (Fin.castLE (by omega) c) s := by
    simp only [applyAff, Fin.val_castLE, if_pos c.isLt]
  simp only [rowOpenings, hc]

theorem h1_applyAff (B : PackBasis F) (u : Trace K) (tape : AffTape K F)
    (r : Fin 1024) : applyAff B u tape 26 r = u 26 r + h1Padding B (Sum.elim 0 tape) r := by
  rfl

/-- At an inactive row every lane is independent of H1. -/
theorem lanes_inactive (pub : Public K) (B : PackBasis F) (u v : Trace K)
    (lam chi : K) (r : Fin 1024) (hr : ¬ CopyActiveRow r)
    (ho : rowOpenings u r = rowOpenings v r) :
    laneAt pub lam chi B (rowOpenings u r) (u 26 r) (rowSel r) =
      laneAt pub lam chi B (rowOpenings v r) (v 26 r) (rowSel r) := by
  funext i
  unfold laneAt
  split_ifs
  · rw [ho]
  · rw [ho]
  · rw [copy_inactive_residuals pub lam chi u r hr,
      copy_inactive_residuals pub lam chi v r hr]

theorem terminal_applyAff (pub : Public K) (B : PackBasis F) (u : Trace K)
    (tape : AffTape K F) (ch : Challenges K) (b : Fin 10 → Bool) :
    terminalValue pub (ch.sem 0) (ch.sem 1) (ch.sem 2) (ch.sem 13) (zc ch) B
      (honestClaims (applyAff B u tape) (ofBool b)) (ofBool b) =
    terminalValue pub (ch.sem 0) (ch.sem 1) (ch.sem 2) (ch.sem 13) (zc ch) B
      (honestClaims u (ofBool b)) (ofBool b) +
      (ch.sem 13 + ch.sem 13 ^ 2) * h1Padding B (Sum.elim 0 tape) (rowOf b) := by
  have ho := openings_applyAff B u tape (rowOf b)
  have hl : laneAt pub (ch.sem 0) (ch.sem 1) B
      (rowOpenings (applyAff B u tape) (rowOf b)) (applyAff B u tape 26 (rowOf b))
      (rowSel (rowOf b)) =
      laneAt pub (ch.sem 0) (ch.sem 1) B (rowOpenings u (rowOf b)) (u 26 (rowOf b))
        (rowSel (rowOf b)) := by
    by_cases ha : CopyActiveRow (rowOf b)
    · rw [ho, h1_applyAff, padding_active B _ _ ha, add_zero]
    · exact lanes_inactive pub B _ u _ _ _ ha ho
  simp only [terminalValue, honestClaims_ofBool, selAt_ofBool]
  change eqValue (zc ch) (ofBool b) *
      (∑ i : Fin 29, ch.sem 2 ^ i.val * laneAt pub _ _ B
        (rowOpenings (applyAff B u tape) (rowOf b)) (applyAff B u tape 26 (rowOf b)) _ i) +
      ch.sem 13 * applyAff B u tape 26 (rowOf b) +
      ch.sem 13 * ch.sem 13 * ((1 - activeAt (ofBool b)) * applyAff B u tape 26 (rowOf b)) = _
  rw [hl, h1_applyAff]
  simp only [rowOpenings]
  by_cases ha : CopyActiveRow (rowOf b)
  · rw [padding_active B _ _ ha]
    ring
  · rw [activeAt_ofBool, copy_active_row, if_neg ha]
    ring

/-- Per-family audit assembled in the terminal's actual lane order. -/
theorem lanes_eligible (pub : Public K) (B : PackBasis F) (t : Trace K)
    (e : EligibleNoise K F) (lam chi : K) (r : Fin 1024) :
    laneAt pub lam chi B (rowOpenings (applyEligible t e) r) (applyEligible t e 26 r) (rowSel r) =
      laneAt pub lam chi B (rowOpenings t r) (t 26 r) (rowSel r) := by
  funext i
  simp only [laneAt, scalarLaneAt, poseidon_eligible, schedule_eligible,
    occupancy_eligible, path_eligible, value_eligible, digest_eligible, asset_eligible,
    copy_eligible]

/-- The stronger row fact needs no honesty premise on the trace. -/
theorem terminal_eligible (pub : Public K) (B : PackBasis F) (t : Trace K)
    (e : EligibleNoise K F) (ch : Challenges K) (b : Fin 10 → Bool) :
    terminalValue pub (ch.sem 0) (ch.sem 1) (ch.sem 2) (ch.sem 13) (zc ch) B
      (honestClaims (applyEligible t e) (ofBool b)) (ofBool b) =
    terminalValue pub (ch.sem 0) (ch.sem 1) (ch.sem 2) (ch.sem 13) (zc ch) B
      (honestClaims t (ofBool b)) (ofBool b) := by
  simp only [terminalValue, honestClaims_ofBool, selAt_ofBool]
  change eqValue (zc ch) (ofBool b) *
      (∑ i : Fin 29, ch.sem 2 ^ i.val * laneAt pub _ _ B
        (rowOpenings (applyEligible t e) (rowOf b)) (applyEligible t e 26 (rowOf b)) _ i) +
      ch.sem 13 * applyEligible t e 26 (rowOf b) +
      ch.sem 13 * ch.sem 13 * ((1 - activeAt (ofBool b)) * applyEligible t e 26 (rowOf b)) = _
  rw [lanes_eligible]
  rfl

theorem prepare_eligible (pub : Public K) (t : Trace K) (e : EligibleNoise K F)
    (ch : Challenges K) :
    prepare pub (applyEligible t e) ch = applyEligible (prepare pub t ch) e := by
  funext c r
  by_cases hc : c.val = 26
  · have h16 : ¬c.val < 16 := by omega
    simp only [prepare, if_pos hc, HelperInvariant.helper_eligible]
    simp only [applyEligible, if_neg h16, prepare, if_pos hc]
  · simp only [prepare, if_neg hc, applyEligible]

/-- Lemma A, exactly the prepared-trace statement fixed by T2b-1. -/
theorem terminal_row_eligible (pub : Public K) (B : PackBasis F) (t : Trace K)
    (e : EligibleNoise K F) (ch : Challenges K) (b : Fin 10 → Bool) :
    terminalValue pub (ch.sem 0) (ch.sem 1) (ch.sem 2) (ch.sem 13) (zc ch) B
      (honestClaims (prepare pub (applyEligible t e) ch) (ofBool b)) (ofBool b) =
    terminalValue pub (ch.sem 0) (ch.sem 1) (ch.sem 2) (ch.sem 13) (zc ch) B
      (honestClaims (prepare pub t ch) (ofBool b)) (ofBool b) := by
  rw [prepare_eligible, terminal_eligible]

#print axioms terminal_row_eligible

#print axioms terminal_applyAff
#print axioms h1Padding_bsumB
end R0Z.TerminalEligible
