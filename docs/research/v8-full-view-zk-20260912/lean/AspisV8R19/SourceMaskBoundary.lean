import AspisV8R19.SourceEncodedOpening

/-! Compose the legal G correction and its retained observation kernel.
Raw/final statements here are the four-channel quotient evaluator statements;
their composition with Rust's actual circle evaluator remains a source task. -/
namespace AspisR19.SourceMaskBoundary
open AspisV8R16 AspisV8R17 AspisCircleTensorBinding HighRepairInvariant
open NormalizedGCore SourceMaskTransport SourceEncodedOpening T163SourceTable
noncomputable section
variable {F : Type*} [Field F] [NeZero (2 : F)]

theorem quotient_image_tail (q : Index 32 → F) (b c : F) :
    flatten q 1023=0 ∧ b*flatten q 1022-c*flatten q 1021=0 := by
  simp [flatten]

theorem chord_truncation_safe (q : Index 32 → F) (a b c : F) :
    ∀ r, 1024≤r → sourceChord (2:F)⁻¹ (flatten q) a b c r=0 := by
  intro r hr
  exact flattened_chord_tail q a b c r (by omega)

theorem normalized_legal_G_boundary (t : Fin 22 → F) (ht : Function.Injective t)
    (alpha x0 y0 x1 y1 : F) (h0 : x0^2+y0^2=1) (h1 : x1^2+y1^2=1) (j : Fin 13) :
    let q := NormalizedQuotient.quotient t ht alpha (SparseHighWitness.degree j) (SparseHighWitness.slot j)
    let a := x0*y1-y0*x1
    let b := y0-y1
    let c := x1-x0
    let m := mask (2:F)⁻¹ a b c q
    transport inactive 1023 order m=code (2:F)⁻¹ a b c q ∧
    (∑ r ∈ inactive, m r)=0 ∧
    (∀ i, mixedCoin m i=0) ∧
    encodedOpening m x0 y0=0 ∧ encodedOpening m x1 y1=0 ∧
    (flatten q 1023=0 ∧ b*flatten q 1022-c*flatten q 1021=0) ∧
    (∀ r, 1024≤r → sourceChord (2:F)⁻¹ (flatten q) a b c r=0) ∧
    (∀ k l, NormalizedQuerySection.evaluate (fun i => q (i,k)) (t l)=0) ∧
    (∀ i, ∑ k : Fin 4, alpha^k.val*q (i,k)=0) := by
  dsimp only
  exact ⟨mask_transport _ _ _ _ _,mask_balanced _ _ _ _ _,
    normalized_mask_coins_zero t ht _ _ _ _ _ j,
    mask_first_ood_zero _ _ _ _ _ h0,mask_second_ood_zero _ _ _ _ _ h1,
    quotient_image_tail _ _ _,chord_truncation_safe _ _ _ _,
    fun k l => NormalizedQuotient.quotient_root t ht _ _ _ k l,
    NormalizedQuotient.quotient_fold t ht _ _ _⟩

#print axioms quotient_image_tail
#print axioms chord_truncation_safe
#print axioms normalized_legal_G_boundary
end
end AspisR19.SourceMaskBoundary
