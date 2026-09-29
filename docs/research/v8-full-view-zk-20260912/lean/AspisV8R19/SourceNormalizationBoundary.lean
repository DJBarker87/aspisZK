import AspisV8R19.NormalizationLoopBridge

namespace AspisR19.SourceNormalizationBoundary
open AspisV8R16 AspisV8R17 NormalizationLoopBridge
open SourceMaskTransport SourceEncodedOpening NormalizedGCore T163SourceTable
noncomputable section
variable {F : Type*} [Field F] [NeZero (2 : F)]

/-- The exact-field sequential normalization inherits the retained legal-G
boundary. This does not postulate or establish a shared-oracle law. -/
theorem source_legal_G_boundary (t : Fin 22 → F) (ht : Function.Injective t)
    (alpha x0 y0 x1 y1 : F) (h0 : x0^2+y0^2=1) (h1 : x1^2+y1^2=1) (j : Fin 13) :
    let q := sourceQuotient t alpha (SparseHighWitness.degree j) (SparseHighWitness.slot j)
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
  rw [selected_sourceQuotient_eq t ht alpha j]
  exact SourceMaskBoundary.normalized_legal_G_boundary t ht alpha x0 y0 x1 y1 h0 h1 j

#print axioms source_legal_G_boundary
end
end AspisR19.SourceNormalizationBoundary
