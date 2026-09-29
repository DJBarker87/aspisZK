import AspisV8R19.FullCoefficientBoundary

/-! One normalized column now has point and relation functionals in the same
full-support model as its raw/OOD/final observations. No rank/probability
conclusion or machine-word refinement is asserted here. -/
namespace AspisR19.FullResidualBoundary
open AspisV8R16 AspisV8R17 T163SourceTable HighRepairInvariant BetaUniformCorrection
open NormalizedGCore SourceMaskTransport FullQuotientWeights FullCoefficientBoundary
noncomputable section
variable {F : Type*} [Field F] [NeZero (2 : F)]

theorem flattened_pairing (q : Index 32 → F) (w : Nat → F) :
    rangeDot 1024 w (flatten q)=∑ i : Index 32,q i*w (4*i.1.val+i.2.val) := by
  unfold rangeDot
  rw [show (1024:Nat)=128+896 by decide,Finset.sum_range_add]
  have hz : (∑ i ∈ Finset.range 896,w (128+i)*flatten q (128+i))=0 := by
    apply Finset.sum_eq_zero
    intro i _
    simp [flatten,show ¬128+i<128 by omega]
  rw [hz,add_zero]
  change (∑ i ∈ Finset.range (4*32),w i*flatten q i)=_
  rw [CircleChannelsBridge.sum_quads,Finset.sum_range,Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro d _
  have h0 := low_slot q d (0:Fin 4)
  have h1 := low_slot q d (1:Fin 4)
  have h2 := low_slot q d (2:Fin 4)
  have h3 := low_slot q d (3:Fin 4)
  simp at h0 h1 h2 h3
  simp [Fin.sum_univ_succ,h0,h1,h2,h3]
  ring

theorem mask_point_dot (half a b c : F) (q : Index 32 → F) (w : Fin 1024 → F) :
    (∑ r : Fin 1024,w r*mask half a b c q r)=
      ∑ i : Index 32,q i*blockWeight half a b c w i := by
  have h := transported_source_opening_pairing half inactive 1023 order w
    (flatten q) a b c (0:F) false
  simp only [Bool.false_eq_true,if_false,zero_mul,zero_pow (by decide : (2:Nat)≠0),
    add_zero] at h
  change rangeDot 1024 (sourceQuotientWeights half
    (extendFin1024 (transportDual inactive 1023 order w)) a b c 0 false)
    (flatten q)=(∑ r : Fin 1024,w r*mask half a b c q r) at h
  rw [← h,flattened_pairing]
  apply Finset.sum_congr rfl
  intro i _
  rw [quotient_entry half a b c 0 false w ⟨4*i.1.val+i.2.val,by omega⟩]
  rfl

theorem source_point (half a b c : F) (q : Index 32 → F) (z : Fin 10 → F) :
    sourcePointFunctional z (mask half a b c q)=
      ∑ i : Index 32,q i*blockWeight half a b c (fun r => sourcePointBasis z r.val) i := by
  exact mask_point_dot half a b c q (fun r => sourcePointBasis z r.val)

theorem normalized_source_point (t : Fin 22 → F) (ht : Function.Injective t)
    (alpha : F) (j : Fin 13) (a b c : F) (z : Fin 10 → F) :
    sourcePointFunctional z (mask (2:F)⁻¹ a b c (SourceCircleBoundary.column t alpha j))=
      ∑ i : Index 32,
        NormalizedQuotient.quotient t ht alpha (SparseHighWitness.degree j) (SparseHighWitness.slot j) i*
        blockWeight (2:F)⁻¹ a b c (fun r => sourcePointBasis z r.val) i := by
  rw [source_point,SourceCircleBoundary.column,NormalizationLoopBridge.selected_sourceQuotient_eq t ht alpha j]

theorem normalized_source_coefficient (t : Fin 22 → F) (ht : Function.Injective t)
    (alpha : F) (j : Fin 13) (a b c tau quarter : F) (structured : Bool)
    (w : Fin 1024 → F) (k : Fin 7) :
    coefficient (sourceKernel 256 k.val quarter)
      (fun i => flatten (SourceCircleBoundary.column t alpha j) (4*i.1.val+i.2.val))
      (fun i => sourceQuotientWeights (2:F)⁻¹
        (extendFin1024 (transportDual inactive 1023 order w))
        a b c tau structured (4*i.1.val+i.2.val)) =
    coefficient (sourceKernel 32 k.val quarter)
      (NormalizedQuotient.quotient t ht alpha (SparseHighWitness.degree j) (SparseHighWitness.slot j))
      (blockWeight (2:F)⁻¹ a b c w) := by
  rw [source_coefficient,SourceCircleBoundary.column,NormalizationLoopBridge.selected_sourceQuotient_eq t ht alpha j]

#print axioms flattened_pairing
#print axioms mask_point_dot
#print axioms source_point
#print axioms normalized_source_point
#print axioms normalized_source_coefficient
end
end AspisR19.FullResidualBoundary
