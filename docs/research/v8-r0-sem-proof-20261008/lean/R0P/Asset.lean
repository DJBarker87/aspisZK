import R0P.Core

/-! G1, pinned ebe7cbcdc315cde4f483f47a79262b8010984e98.
Source T = crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs.
Only the two scalar contributions at slots 92–93, before packing.
Public amounts/assets have already been embedded in K by Core.Public. -/
set_option autoImplicit false
namespace R0P
variable {K : Type} [Field K]

/-- T:1121–1141, scalar_lanes: preserve the addition and presence branch. -/
def assetScalarLanes (variant : Variant) (withdrawalPresent : Bool)
    (inputAsset outputScalar privateTransferTerm withdrawalTerm : K) : List K :=
  let outputScalar := match variant with
    | .privateTransfer => outputScalar + privateTransferTerm
    | .withdrawal => if withdrawalPresent then outputScalar + withdrawalTerm else outputScalar
  [inputAsset, outputScalar]

/-- T:59,1165–1181: exact selectors and unwrap_or(0), then scalar_lanes.
Host public-amount validation is not part of this residual family. -/
def assetFamily : Family K where
  residuals := fun pub o sel =>
    let assetDifference := o.z 1 - pub.assetId
    let inputAsset := sel (2*16+12) * assetDifference
    let outputScalar := sel (31*16+12) * assetDifference
    let privateTransferTerm := sel (28*16+12) * assetDifference
    let withdrawalAmountValue := pub.withdrawalAmount.getD 0
    let withdrawalTerm := sel (16*63+2) * (o.z 10 - withdrawalAmountValue)
    assetScalarLanes pub.variant pub.withdrawalAmount.isSome inputAsset outputScalar
      privateTransferTerm withdrawalTerm

theorem asset_selected_iff (i : Fin 1024) (x : Fin 1024 → K) :
    (∀ b, rowSel b i * x b = 0) ↔ x i = 0 := by
  constructor
  · intro h
    simpa only [rowSel_self, one_mul] using h i
  · intro h b
    by_cases hb : i = b
    · subst b
      simpa only [rowSel_self, one_mul] using h
    · rw [rowSel_ne b i hb, zero_mul]

theorem asset_selected_add_iff (i j : Fin 1024) (hij : i ≠ j)
    (x y : Fin 1024 → K) :
    (∀ b, rowSel b i * x b + rowSel b j * y b = 0) ↔ x i = 0 ∧ y j = 0 := by
  constructor
  · intro h
    constructor
    · simpa only [rowSel_self, rowSel_ne i j (Ne.symm hij), one_mul, zero_mul,
        add_zero] using h i
    · simpa only [rowSel_self, rowSel_ne j i hij, one_mul, zero_mul,
        zero_add] using h j
  · rintro ⟨hx,hy⟩ b
    by_cases hi : i = b
    · subst b
      rw [rowSel_self, rowSel_ne i j (Ne.symm hij), one_mul, zero_mul, add_zero, hx]
    · by_cases hj : j = b
      · subst b
        rw [rowSel_self, rowSel_ne j i hij, one_mul, zero_mul, zero_add, hy]
      · rw [rowSel_ne b i hi, rowSel_ne b j hj, zero_mul, zero_mul, zero_add]

theorem asset_holds_iff (pub : Public K) (A : Trace K) :
    Holds assetFamily pub A ↔
      A 1 44 = pub.assetId ∧ A 1 508 = pub.assetId ∧
      (pub.variant = .privateTransfer → A 1 460 = pub.assetId) ∧
      (pub.variant = .withdrawal → ∀ amount,
        pub.withdrawalAmount = some amount → A 10 1010 = amount) := by
  unfold Holds assetFamily assetScalarLanes
  cases hv : pub.variant <;> cases ha : pub.withdrawalAmount
  all_goals
    simp only [hv, ha, Option.isSome_none, Option.isSome_some, Option.getD_none, Option.getD_some,
      Bool.false_eq_true, ite_false, ite_true,
      List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true, forall_and, rowOpenings]
  all_goals
    change ((∀ b, rowSel b 44 * (A 1 b-pub.assetId) = 0) ∧ _) ↔ _
    rw [asset_selected_iff]
  · change (A 1 44-pub.assetId = 0 ∧
      (∀ b, rowSel b 508*(A 1 b-pub.assetId) + rowSel b 460*(A 1 b-pub.assetId) = 0)) ↔ _
    rw [asset_selected_add_iff 508 460 (by decide)]
    simp [sub_eq_zero]
  · change (A 1 44-pub.assetId = 0 ∧
      (∀ b, rowSel b 508*(A 1 b-pub.assetId) + rowSel b 460*(A 1 b-pub.assetId) = 0)) ↔ _
    rw [asset_selected_add_iff 508 460 (by decide)]
    simp [sub_eq_zero]
  · rw [asset_selected_iff]
    simp [sub_eq_zero]
  · rename_i amount
    change (A 1 44-pub.assetId = 0 ∧
      (∀ b, rowSel b 508*(A 1 b-pub.assetId) + rowSel b 1010*(A 10 b-amount) = 0)) ↔ _
    rw [asset_selected_add_iff 508 1010 (by decide)]
    simp [sub_eq_zero]

#print axioms asset_selected_iff
#print axioms asset_selected_add_iff
#print axioms asset_holds_iff
end R0P
