import R0P.Copy
import CopyActiveMaskBasisFacts

set_option autoImplicit false
namespace R0P

variable {K : Type} [Field K]

/-- The seven constant masks in the frozen 64-block active schedule. -/
def activeMaskBasisMasks : Fin 7 → Nat := ![6144, 6145, 4097, 2048, 2049, 26214, 1749]

def activeMaskCoordinate (mask : Nat) : Fin 7 :=
  match mask with
  | 6144 => 0
  | 6145 => 1
  | 4097 => 2
  | 2048 => 3
  | 2049 => 4
  | 26214 => 5
  | 1749 => 6
  | _ => 0

def activeMaskLowSum (low : Fin 16 → K) (mask : Nat) : K :=
  match mask with
  | 6144 => low 11 + low 12
  | 6145 => low 0 + low 11 + low 12
  | 4097 => low 0 + low 12
  | 2048 => low 11
  | 2049 => low 0 + low 11
  | 26214 => low 1 + low 2 + low 5 + low 6 + low 9 + low 10 + low 13 + low 14
  | 1749 => low 0 + low 2 + low 4 + low 6 + low 7 + low 9 + low 10
  | _ => 0

def activeMaskGroupedHigh (high : Fin 64 → K) (coord : Fin 7) : K :=
  ∑ block : Fin 64,
    if activeMaskCoordinate (copyActiveRowMasks block) = coord then high block else 0

def activeMaskBasisModel (s : CopySelectors K) : K :=
  ∑ coord : Fin 7,
    activeMaskGroupedHigh s.high coord * activeMaskLowSum s.low (activeMaskBasisMasks coord)

private theorem active_masks_are_basis_members (block : Fin 64) :
    copyActiveRowMasks block = 6144 ∨ copyActiveRowMasks block = 6145 ∨
    copyActiveRowMasks block = 4097 ∨ copyActiveRowMasks block = 2048 ∨
    copyActiveRowMasks block = 2049 ∨ copyActiveRowMasks block = 26214 ∨
    copyActiveRowMasks block = 1749 := by
  fin_cases block <;> decide

private theorem active_mask_has_coordinate (block : Fin 64) :
    activeMaskBasisMasks (activeMaskCoordinate (copyActiveRowMasks block)) =
      copyActiveRowMasks block := by
  rcases active_masks_are_basis_members block with h | h | h | h | h | h | h <;>
    simp [activeMaskCoordinate, activeMaskBasisMasks, h]

private theorem active_mask_low_sum_correct (low : Fin 16 → K) (mask : Nat)
    (hm : mask = 6144 ∨ mask = 6145 ∨ mask = 4097 ∨ mask = 2048 ∨
      mask = 2049 ∨ mask = 26214 ∨ mask = 1749) :
    copySelectorMaskSum16 low mask = activeMaskLowSum low mask := by
  rcases hm with h | h | h | h | h | h | h <;> subst mask <;>
    simp [activeMaskLowSum, copy_selector_mask_sum_6144,
      copy_selector_mask_sum_6145, copy_selector_mask_sum_4097,
      copy_selector_mask_sum_2048, copy_selector_mask_sum_2049,
      copy_selector_mask_sum_26214, copy_selector_mask_sum_1749]

/-- Finite-sum regrouping identity: terms may be grouped by any finite key.
This is the algebraic bridge from block-order accumulation to seven mask
coordinates; no selector-domain premise is required. -/
theorem finset_sum_regroup_by_key {α β : Type} [Fintype α] [Fintype β]
    [DecidableEq β] (key : α → β) (term : α → K) (weight : β → K) :
    (∑ a : α, term a * weight (key a)) =
      ∑ b : β, (∑ a : α, if key a = b then term a else 0) * weight b := by
  classical
  calc
    (∑ a : α, term a * weight (key a)) =
        ∑ a : α, ∑ b : β, (if key a = b then term a else 0) * weight b := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [Finset.sum_eq_single (key a)]
      · simp
      · intro b hb hba
        by_cases heq : key a = b
        · exact False.elim (hba heq.symm)
        · simp [heq]
      · intro hnot
        exact False.elim (hnot (Finset.mem_univ _))
    _ = ∑ b : β, ∑ a : α, (if key a = b then term a else 0) * weight b := by
      rw [Finset.sum_comm]
    _ = ∑ b : β, (∑ a : α, if key a = b then term a else 0) * weight b := by
      simp_rw [← Finset.sum_mul]

def activeMaskContribution (s : CopySelectors K) (block : Fin 64) : K :=
  if copyActiveRowMasks block ≠ 0 then
    s.high block * copySelectorMaskSum16 s.low (copyActiveRowMasks block) else 0

private theorem active_mask_fold_add {α : Type} (xs : List α) (f : α → K) (a : K) :
    xs.foldl (fun acc x => acc + f x) a = a + (xs.map f).sum := by
  induction xs generalizing a with
  | nil => simp only [List.foldl_nil, List.map_nil, List.sum_nil, add_zero]
  | cons x xs ih =>
    simp only [List.foldl_cons, ih, List.map_cons, List.sum_cons, add_assoc]

private theorem active_literal_as_sum (s : CopySelectors K) :
    copyActiveLiteral s = ∑ block : Fin 64, activeMaskContribution s block := by
  unfold copyActiveLiteral
  have hstep :
      (fun (sum : K) (block : Fin 64) =>
        if copyActiveRowMasks block ≠ 0 then
          sum + s.high block * copySelectorMaskSum16 s.low (copyActiveRowMasks block)
        else sum) =
      (fun sum block => sum + activeMaskContribution s block) := by
    funext sum block
    by_cases h : copyActiveRowMasks block ≠ 0 <;> simp [activeMaskContribution, h]
  rw [hstep, active_mask_fold_add, zero_add, List.map_ofFn, List.sum_ofFn]
  rfl

/-- The grouped seven-mask field formula equals the literal selector evaluation
for every pair of selector vectors, including arbitrary off-domain values. -/
theorem copy_active_literal_eq_active_mask_basis (s : CopySelectors K) :
    copyActiveLiteral s = activeMaskBasisModel s := by
  rw [active_literal_as_sum]
  have hnonzero (block : Fin 64) : copyActiveRowMasks block ≠ 0 := by
    rcases active_masks_are_basis_members block with h | h | h | h | h | h | h <;>
      simp [h]
  have hlow (block : Fin 64) :
      copySelectorMaskSum16 s.low (copyActiveRowMasks block) =
        activeMaskLowSum s.low (activeMaskBasisMasks
          (activeMaskCoordinate (copyActiveRowMasks block))) := by
    rw [active_mask_has_coordinate block]
    apply active_mask_low_sum_correct
    exact active_masks_are_basis_members block
  simp only [activeMaskContribution, if_pos (hnonzero _), hlow]
  simpa [activeMaskBasisModel, activeMaskGroupedHigh] using
    (finset_sum_regroup_by_key
      (key := fun block : Fin 64 => activeMaskCoordinate (copyActiveRowMasks block))
      (term := s.high) (weight := fun coord =>
        activeMaskLowSum s.low (activeMaskBasisMasks coord)))

#print axioms copy_active_literal_eq_active_mask_basis
#print axioms finset_sum_regroup_by_key

end R0P
