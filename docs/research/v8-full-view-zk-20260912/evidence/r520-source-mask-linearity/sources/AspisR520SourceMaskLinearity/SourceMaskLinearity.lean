import AspisV8R19.CircleObservationBridge

namespace AspisR520SourceMaskLinearity

open scoped BigOperators
open AspisV8R16
open AspisR19.CircleObservationBridge
open AspisR19.CircleChannelsBridge AspisR19.T163SourceTable

noncomputable section
variable {F : Type*} [Field F]

private theorem sourceEvaluate_add (u v : Nat → F) (x y : F) :
    sourceEvaluate (u + v) x y = sourceEvaluate u x y + sourceEvaluate v x y := by
  unfold sourceEvaluate
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro r hr
  simp [Pi.add_apply]
  ring

private theorem sourceEvaluate_mul (c : F) (u : Nat → F) (x y : F) :
    sourceEvaluate (fun r => c * u r) x y = c * sourceEvaluate u x y := by
  unfold sourceEvaluate
  calc
    _ = ∑ r ∈ Finset.range 1024, c * (AspisR19.CircleWeightBridge.sourceWeight x y r * u r) := by
      apply Finset.sum_congr rfl
      intro r hr
      ring
    _ = _ := by rw [Finset.mul_sum]

private theorem sourceEvaluate_zero (x y : F) : sourceEvaluate (0 : Nat → F) x y = 0 := by
  unfold sourceEvaluate
  simp

private theorem transported_add (m n : Fin 1024 → F) (r : Nat) :
    (if h : r < 1024 then
      transport AspisR19.T163SourceTable.inactive 1023 AspisR19.T163SourceTable.order (m + n) ⟨r, h⟩ else 0) =
    (if h : r < 1024 then
      transport AspisR19.T163SourceTable.inactive 1023 AspisR19.T163SourceTable.order m ⟨r, h⟩ else 0) +
    (if h : r < 1024 then
      transport AspisR19.T163SourceTable.inactive 1023 AspisR19.T163SourceTable.order n ⟨r, h⟩ else 0) := by
  by_cases hr : r < 1024
  · simp only [dif_pos hr]
    exact congrFun (transport_add _ _ _ m n) (⟨r, hr⟩ : Fin 1024)
  · simp only [dif_neg hr, add_zero]

private theorem transported_mul (c : F) (m : Fin 1024 → F) (r : Nat) :
    (if h : r < 1024 then
      transport AspisR19.T163SourceTable.inactive 1023 AspisR19.T163SourceTable.order (fun i => c * m i) ⟨r, h⟩ else 0) =
    c * (if h : r < 1024 then
      transport AspisR19.T163SourceTable.inactive 1023 AspisR19.T163SourceTable.order m ⟨r, h⟩ else 0) := by
  by_cases hr : r < 1024
  · simp only [dif_pos hr, transport]
    split
    · rw [Finset.mul_sum]
    · rfl
  · simp only [dif_neg hr, mul_zero]

theorem sourceMaskEvaluate_add (m n : Fin 1024 → F) (x y : F) :
    sourceMaskEvaluate (m + n) x y = sourceMaskEvaluate m x y + sourceMaskEvaluate n x y := by
  unfold sourceMaskEvaluate
  rw [show (fun r => if h : r < 1024 then
      transport AspisR19.T163SourceTable.inactive 1023 AspisR19.T163SourceTable.order (m + n) ⟨r, h⟩ else 0) =
      (fun r => if h : r < 1024 then
        transport AspisR19.T163SourceTable.inactive 1023 AspisR19.T163SourceTable.order m ⟨r, h⟩ else 0) +
      (fun r => if h : r < 1024 then
        transport AspisR19.T163SourceTable.inactive 1023 AspisR19.T163SourceTable.order n ⟨r, h⟩ else 0) by
        funext r; exact transported_add m n r]
  exact sourceEvaluate_add _ _ x y

theorem sourceMaskEvaluate_mul (c : F) (m : Fin 1024 → F) (x y : F) :
    sourceMaskEvaluate (fun i => c * m i) x y = c * sourceMaskEvaluate m x y := by
  unfold sourceMaskEvaluate
  rw [show (fun r => if h : r < 1024 then
      transport AspisR19.T163SourceTable.inactive 1023 AspisR19.T163SourceTable.order (fun i => c * m i) ⟨r, h⟩ else 0) =
      (fun r => c * (if h : r < 1024 then
        transport AspisR19.T163SourceTable.inactive 1023 AspisR19.T163SourceTable.order m ⟨r, h⟩ else 0)) by
        funext r; exact transported_mul c m r]
  exact sourceEvaluate_mul c _ x y

private theorem sourceMaskEvaluate_zero (x y : F) : sourceMaskEvaluate (0 : Fin 1024 → F) x y = 0 := by
  unfold sourceMaskEvaluate
  rw [show (fun r => if h : r < 1024 then
      transport AspisR19.T163SourceTable.inactive 1023 AspisR19.T163SourceTable.order (0 : Fin 1024 → F) ⟨r, h⟩ else 0) = 0 by
        funext r
        by_cases hr : r < 1024
        · simp only [dif_pos hr, transport]
          split <;> simp
        · simp [hr]]
  exact sourceEvaluate_zero x y

theorem sourceMaskEvaluate_fin_sum {n : Nat} (m : Fin n → Fin 1024 → F) (x y : F) :
    sourceMaskEvaluate (fun i => ∑ k : Fin n, m k i) x y =
      ∑ k : Fin n, sourceMaskEvaluate (m k) x y := by
  classical
  have hsum : (fun i => ∑ k : Fin n, m k i) = ∑ k : Fin n, m k := by
    funext i
    simp
  rw [hsum]
  have map_sum : ∀ s : Finset (Fin n),
      sourceMaskEvaluate (∑ k ∈ s, m k) x y = ∑ k ∈ s, sourceMaskEvaluate (m k) x y := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp [sourceMaskEvaluate_zero]
    | insert a s ha ih =>
      rw [Finset.sum_insert ha, sourceMaskEvaluate_add, ih, Finset.sum_insert ha]
  exact map_sum Finset.univ

theorem sourceMaskEvaluate_weighted_fin_sum {n : Nat} (w : Fin n → F)
    (m : Fin n → Fin 1024 → F) (x y : F) :
    sourceMaskEvaluate (fun i => ∑ k : Fin n, w k * m k i) x y =
      ∑ k : Fin n, w k * sourceMaskEvaluate (m k) x y := by
  rw [sourceMaskEvaluate_fin_sum]
  apply Finset.sum_congr rfl
  intro k hk
  exact sourceMaskEvaluate_mul (w k) (m k) x y

#print axioms sourceMaskEvaluate_add
#print axioms sourceMaskEvaluate_mul
#print axioms sourceMaskEvaluate_fin_sum
#print axioms sourceMaskEvaluate_weighted_fin_sum

end
end AspisR520SourceMaskLinearity
