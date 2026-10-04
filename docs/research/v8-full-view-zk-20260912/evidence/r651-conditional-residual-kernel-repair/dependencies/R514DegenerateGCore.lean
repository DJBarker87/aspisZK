import AspisV8R19.R513SourceDegenerateRoots

/-! Exact-field source-shaped G preservation for arbitrary query roots.
This does not prove correction coverage, C1/H1 compatibility or Rust execution. -/
set_option autoImplicit false
namespace AspisR19.R514DegenerateGCore
open AspisV8R17
open NormalizationLoopBridge NormalizedQuotient NormalizedGCore
open SourceMaskTransport HighRepairInvariant HighQueryGCore
open scoped BigOperators
variable {F : Type*} [Field F] [NeZero (2 : F)]

theorem source_quotient_high (t : Fin 22 → F) (alpha : F)
    (d : Fin 32) (hd : 22 ≤ d.val) (s : Fin 4) (hs : s ≠ 0)
    (i : Fin 32 × Fin 4) (hi : 22 ≤ i.1.val) :
    sourceQuotient t alpha d s i = HighRepairInvariant.column alpha d s i := by
  have hr := DescendingRemainder.remainder_support (List.ofFn t) (by simp) d hd i.1.val hi
  rw [R511SourceDegenerateFold.source_quotient_slot_factor t alpha d s i.2 hs i.1]
  simp only [finished, hr, neg_zero]
  by_cases hid : i.1 = d <;> by_cases hs0 : i.2 = 0 <;> by_cases his : i.2 = s <;>
    simp_all [HighRepairInvariant.column, HighRepairInvariant.unit, slotFactor, Prod.ext_iff]

theorem selected_degree_high (j : Fin 13) : 22 ≤ (SparseHighWitness.degree j).val := by
  simp only [SparseHighWitness.degree]
  split_ifs <;> omega

theorem selected_slot_nonzero (j : Fin 13) : SparseHighWitness.slot j ≠ 0 := by
  intro h
  have hv := congrArg Fin.val h
  simp only [SparseHighWitness.slot, Fin.val_zero] at hv
  split_ifs at hv

theorem source_selected_g_zero (t : Fin 22 → F)
    (half alpha a b c : F) (j : Fin 13) (i : Fin 271) :
    sourceChord half (flatten (SourceCircleBoundary.column t alpha j))
      a b c (128 + 3 * i.val) = 0 := by
  unfold SourceCircleBoundary.column
  rw [low_repair_preserves_g half _
    (flatten (HighRepairInvariant.column alpha (SparseHighWitness.degree j) (SparseHighWitness.slot j)))
    (flatten_high _ _ (fun r hr => source_quotient_high t alpha _
      (selected_degree_high j) _ (selected_slot_nonzero j) r hr)) a b c i]
  exact selected_direct_g_zero half alpha a b c j i

theorem source_mask_coins_zero (t : Fin 22 → F)
    (half alpha a b c : F) (j : Fin 13) (i : Fin 271) :
    mixedCoin (mask half a b c (SourceCircleBoundary.column t alpha j)) i = 0 := by
  rw [mask_coin]
  exact source_selected_g_zero t half alpha a b c j i

/-- The legal-G direction boundary is valid for repeated roots, zero alpha,
and coincident OOD points. No claim that these directions cover all required
joint C1/H1/G targets is made. -/
theorem source_legal_G_boundary (t : Fin 22 → F)
    (alpha x0 y0 x1 y1 : F) (h0 : x0^2 + y0^2 = 1)
    (h1 : x1^2 + y1^2 = 1) (j : Fin 13) :
    let q := SourceCircleBoundary.column t alpha j
    let a := x0*y1 - y0*x1
    let b := y0 - y1
    let c := x1 - x0
    let m := mask (2:F)⁻¹ a b c q
    AspisV8R16.transport T163SourceTable.inactive 1023 T163SourceTable.order m = code (2:F)⁻¹ a b c q ∧
    (∑ r ∈ T163SourceTable.inactive, m r) = 0 ∧
    (∀ i, mixedCoin m i = 0) ∧
    SourceEncodedOpening.encodedOpening m x0 y0 = 0 ∧
    SourceEncodedOpening.encodedOpening m x1 y1 = 0 ∧
    (flatten q 1023 = 0 ∧ b * flatten q 1022 - c * flatten q 1021 = 0) ∧
    (∀ r, 1024 ≤ r → sourceChord (2:F)⁻¹ (flatten q) a b c r = 0) ∧
    (∀ k l, NormalizedQuerySection.evaluate (fun i => q (i,k)) (t l) = 0) ∧
    (∀ i, ∑ k : Fin 4, alpha^k.val * q (i,k) = 0) := by
  dsimp only
  refine ⟨mask_transport _ _ _ _ _, mask_balanced _ _ _ _ _,
    source_mask_coins_zero t _ _ _ _ _ j,
    SourceEncodedOpening.mask_first_ood_zero _ _ _ _ _ h0,
    SourceEncodedOpening.mask_second_ood_zero _ _ _ _ _ h1,
    SourceMaskBoundary.quotient_image_tail _ _ _,
    SourceMaskBoundary.chord_truncation_safe _ _ _ _,
    fun k l => R513SourceDegenerateRoots.selected_column_slot_root_zero t alpha j k l, ?_⟩
  intro i
  simpa only [R370KernelEvaluation.firstFold, mul_comm] using
    R511SourceDegenerateFold.selected_column_first_fold_zero t alpha j i

/-- Division guards remain explicit; this is not a proof that source Domain
failure is impossible. -/
theorem source_prepared_final_zero (t : Fin 22 → F) (alpha : F) (j : Fin 13)
    (a b c x y : F) (circle : x^2 + y^2 = 1) (hx : x ≠ 0) (hy : y ≠ 0)
    (l0 : a + b*x + c*y ≠ 0) (l1 : a + b*x + c*(-y) ≠ 0)
    (l2 : a + b*(-x) + c*(-y) ≠ 0) (l3 : a + b*(-x) + c*y ≠ 0) :
    let m := mask (2:F)⁻¹ a b c (SourceCircleBoundary.column t alpha j)
    PreparedCircleFold.polynomialFold (2*x)⁻¹ (2*y)⁻¹ alpha
      (CircleObservationBridge.sourceMaskEvaluate m x y / (a+b*x+c*y))
      (CircleObservationBridge.sourceMaskEvaluate m x (-y) / (a+b*x+c*(-y)))
      (CircleObservationBridge.sourceMaskEvaluate m (-x) (-y) / (a+b*(-x)+c*(-y)))
      (CircleObservationBridge.sourceMaskEvaluate m (-x) y / (a+b*(-x)+c*y)) = 0 := by
  apply PreparedCircleFold.prepared_mask_final_zero
      (SourceCircleBoundary.column t alpha j) alpha ?_ a b c x y circle hx hy l0 l1 l2 l3
  intro i
  simpa only [R370KernelEvaluation.firstFold, mul_comm] using
    R511SourceDegenerateFold.selected_column_first_fold_zero t alpha j i

#print axioms source_legal_G_boundary
#print axioms source_prepared_final_zero

#print axioms source_quotient_high
#print axioms selected_degree_high
#print axioms selected_slot_nonzero
#print axioms source_selected_g_zero
#print axioms source_mask_coins_zero
end AspisR19.R514DegenerateGCore
