import AspisV8R19.TwoSwapSourceFixed
import AspisV8R19.SourceStatementPoints

/-! Full 131-output/128-input residual model. The scalar query sections are
fixed parameters, not new random or independently resampled coordinates. -/
namespace AspisR19.TwoSwapResidualModel
open AspisV8R17 HighRepairInvariant BetaUniformCorrection TwoSwapSourceWeights
noncomputable section
variable {F G : Type*} [CommRing F] [CommRing G]

def column (v : Fin 13 → Fin 32 → F) (alpha : F) (j : Fin 13) (i : Index 32) : F :=
  v j i.1*((if i.2=TwoSwapWitness.slot j then 1 else 0)-
    alpha^(TwoSwapWitness.slot j).val*(if i.2=0 then 1 else 0))

def pointWeight (half a b c : F) (z : Fin 10 → F) (which : Nat) (i : Index 32) : F :=
  TwoSwapSourceWeights.pointWeight half a b c
    (fun r => sourcePointBasis (ResidualModel.point z which) r.val)
    ⟨4*i.1.val+i.2.val,by omega⟩

def gBoundary (half a b c : F) (i : Index 32) : F :=
  half^10*ResidualModel.chordEntry half a b c (4*i.1.val+i.2.val) 128

def weight (half a b c kappa : F) (z : Fin 10 → F) (structured : Bool) (i : Index 32) : F :=
  kappa*(if structured then gBoundary half a b c i else pointWeight half a b c z 0 i)+
    kappa^2*pointWeight half a b c z 1 i+kappa^3*pointWeight half a b c z 2 i

def observed (half quarter a b c kappa : F) (z : Fin 10 → F) (q : Index 32 → F) (row : Nat) : F :=
  if row<3 then ∑ i,q i*pointWeight half a b c z row i
  else if row<10 then coefficient (sourceKernel 32 (row-3) quarter) q (weight half a b c kappa z false)
  else coefficient (sourceKernel 32 (row-10) quarter) q (weight half a b c kappa z true)

def matrix (half quarter a b c kappa alpha : F) (z : Fin 10 → F)
    (v : Fin 13 → Fin 32 → F) : Matrix (Fin 13) (Fin 13) F :=
  fun i j => observed half quarter a b c kappa z (column v alpha j) (ResidualModel.selectedRow i)

theorem map_column (f : F →+* G) (v : Fin 13 → Fin 32 → F) (alpha : F) (j : Fin 13) (i : Index 32) :
    f (column v alpha j i)=column (fun j i => f (v j i)) (f alpha) j i := by
  unfold column
  split_ifs <;> simp only [map_mul,map_sub,map_pow,map_one,map_zero]

theorem map_pointWeight (f : F →+* G) (half a b c : F) (z : Fin 10 → F) (which : Nat) (i : Index 32) :
    f (pointWeight half a b c z which i)=pointWeight (f half) (f a) (f b) (f c) (fun j => f (z j)) which i := by
  simp only [pointWeight,TwoSwapSourceFixed.map_weight,TwoSwapSourceFixed.map_point_basis]

theorem map_weight (f : F →+* G) (half a b c kappa : F) (z : Fin 10 → F) (structured : Bool) (i : Index 32) :
    f (weight half a b c kappa z structured i)=
      weight (f half) (f a) (f b) (f c) (f kappa) (fun j => f (z j)) structured i := by
  simp only [weight,gBoundary,map_add,map_mul,map_pow,apply_ite,map_pointWeight,ResidualModel.map_chordEntry]

theorem map_observed (f : F →+* G) (half quarter a b c kappa : F) (z : Fin 10 → F)
    (q : Index 32 → F) (row : Nat) :
    f (observed half quarter a b c kappa z q row)=
      observed (f half) (f quarter) (f a) (f b) (f c) (f kappa) (fun j => f (z j)) (fun i => f (q i)) row := by
  unfold observed
  split_ifs <;> simp only [coefficient,sourceKernel,map_sum,map_mul,apply_ite,map_zero,
    map_pointWeight,map_weight]

theorem map_matrix (f : F →+* G) (half quarter a b c kappa alpha : F) (z : Fin 10 → F)
    (v : Fin 13 → Fin 32 → F) (i j : Fin 13) :
    f (matrix half quarter a b c kappa alpha z v i j)=
      matrix (f half) (f quarter) (f a) (f b) (f c) (f kappa) (f alpha)
        (fun i => f (z i)) (fun j i => f (v j i)) i j := by
  simp only [matrix,map_observed,map_column]

#print axioms map_column
#print axioms map_pointWeight
#print axioms map_weight
#print axioms map_observed
#print axioms map_matrix
end
end AspisR19.TwoSwapResidualModel
