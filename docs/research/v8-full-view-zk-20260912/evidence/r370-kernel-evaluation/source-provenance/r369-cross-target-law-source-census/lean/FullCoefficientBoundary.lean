import AspisV8R19.FullQuotientWeights

/-! Exact finite-field block-kernel restriction for all seven relation
coefficients. This is not a Rust word-semantics extraction. -/
namespace AspisR19.FullCoefficientBoundary
open AspisV8R16 AspisV8R17 BetaUniformCorrection FullQuotientWeights
open T163SourceTable NormalizedGCore HighRepairInvariant
noncomputable section
variable {F : Type*} [CommRing F]

theorem coefficient_blocks (n k : Nat) (quarter : F)
    (q w : Fin n × Fin 4 → F) :
    coefficient (sourceKernel n k quarter) q w =
      ∑ d : Fin n, ∑ s : Fin 4, ∑ t : Fin 4,
        (if s.val+(4-t.val)%4=k then quarter else 0)*q (d,s)*w (d,t) := by
  unfold coefficient
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro d _
  apply Finset.sum_congr rfl
  intro s _
  rw [Fintype.sum_prod_type,Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro t _
  simp [sourceKernel,ite_and,ite_mul]

def blockWeight (half a b c : F) (w : Fin 1024 → F) (i : Index 32) : F :=
  pointWeight half a b c w ⟨4*i.1.val+i.2.val,by omega⟩

theorem low_slot (q : Index 32 → F) (d : Fin 32) (s : Fin 4) :
    flatten q (4*d.val+s.val)=q (d,s) := by
  rw [flatten,dif_pos (show 4*d.val+s.val<128 by omega)]
  congr 1
  apply Prod.ext <;> apply Fin.ext <;> dsimp only <;> omega

theorem source_coefficient (half a b c tau quarter : F) (structured : Bool)
    (w : Fin 1024 → F) (q : Index 32 → F) (k : Nat) :
    coefficient (sourceKernel 256 k quarter)
      (fun i => flatten q (4*i.1.val+i.2.val))
      (fun i => sourceQuotientWeights half
        (extendFin1024 (transportDual inactive 1023 order w))
        a b c tau structured (4*i.1.val+i.2.val)) =
    coefficient (sourceKernel 32 k quarter) q (blockWeight half a b c w) := by
  rw [coefficient_blocks,coefficient_blocks,Fin.sum_univ_add (a:=32) (b:=224)]
  have hz : (∑ d : Fin 224, ∑ s : Fin 4, ∑ t : Fin 4,
      (if s.val+(4-t.val)%4=k then quarter else 0)*
        flatten q (4*(Fin.natAdd 32 d).val+s.val)*
        sourceQuotientWeights half (extendFin1024 (transportDual inactive 1023 order w))
          a b c tau structured (4*(Fin.natAdd 32 d).val+t.val))=0 := by
    apply Finset.sum_eq_zero
    intro d _
    apply Finset.sum_eq_zero
    intro s _
    apply Finset.sum_eq_zero
    intro t _
    simp [flatten,Fin.natAdd,show ¬4*(32+d.val)+s.val<128 by omega]
  rw [hz,add_zero]
  apply Finset.sum_congr rfl
  intro d _
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro t _
  simp only [Fin.val_castAdd,low_slot]
  rw [quotient_entry half a b c tau structured w ⟨4*d.val+t.val,by omega⟩]
  rfl

#print axioms coefficient_blocks
#print axioms low_slot
#print axioms source_coefficient
end
end AspisR19.FullCoefficientBoundary
