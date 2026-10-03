import AspisV8R19.R511SourceDegenerateFold

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

#print axioms source_quotient_high
#print axioms selected_degree_high
#print axioms selected_slot_nonzero
#print axioms source_selected_g_zero
#print axioms source_mask_coins_zero
end AspisR19.R514DegenerateGCore
