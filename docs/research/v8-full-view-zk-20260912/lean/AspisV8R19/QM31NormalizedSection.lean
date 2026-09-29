import AspisV8R19.NormalizedQuotient
import AspisV8R19.HighWitnessFieldTransport
import AspisV8R19.QM31ResidualWitness

/-! Every distinct exact-QM31 root tuple admits the new fixed-specialization
raw/fold-zero residual section. This is not the full source residual theorem:
the source G core/support bridge, challenge-dependent polynomial and its
source conditional law are not supplied by this fixed matrix statement. -/
namespace AspisR19.QM31NormalizedSection
open AspisV8R15.ExactTowerBase QM31ResidualWitness SparseHighWitness
open HighRepairInvariant NormalizedQuotient
noncomputable section

local instance : NeZero (2 : QM31Exact) := ⟨by
  intro h
  have hz : (2 : RootCertificate.M)=0 := by
    apply embed_injective
    simpa only [map_ofNat,map_zero] using h
  exact (by decide : (2 : RootCertificate.M) ≠ 0) hz⟩

def columns (t : Fin 22 → QM31Exact) (ht : Function.Injective t)
    (j : Fin 13) : Index 32 → QM31Exact :=
  quotient t ht (embed 7) (degree j) (slot j)

theorem columns_high (t : Fin 22 → QM31Exact) (ht : Function.Injective t)
    (j : Fin 13) (i : Index 32) (hi : 22 ≤ i.1.val) :
    columns t ht j i = embed (column (7 : RootCertificate.M) (degree j) (slot j) i) := by
  rw [columns,quotient_high t ht _ _ _ i hi]
  simp only [column,unit,map_sub,map_mul,map_pow]
  split_ifs <;> simp_all

def matrix (t : Fin 22 → QM31Exact) (ht : Function.Injective t) :
    Matrix (Fin 13) (Fin 13) QM31Exact :=
  HighWitnessFieldTransport.matrix embed (columns t ht)

theorem matrix_independent_of_roots (t : Fin 22 → QM31Exact) (ht : Function.Injective t) :
    matrix t ht = SparseHighWitness.matrix.map embed :=
  HighWitnessFieldTransport.matrix_equal embed _ (columns_high t ht)

theorem det_ne_zero (t : Fin 22 → QM31Exact) (ht : Function.Injective t) :
    (matrix t ht).det ≠ 0 :=
  HighWitnessFieldTransport.repaired_det_ne_zero embed embed_injective _ (columns_high t ht)

theorem selected_residual_surjective (t : Fin 22 → QM31Exact) (ht : Function.Injective t) :
    Function.Surjective (matrix t ht).mulVec := by
  apply Matrix.mulVec_surjective_iff_isUnit.mpr
  apply (Matrix.isUnit_iff_isUnit_det _).mpr
  exact isUnit_iff_ne_zero.mpr (det_ne_zero t ht)

theorem columns_root_zero (t : Fin 22 → QM31Exact) (ht : Function.Injective t)
    (j : Fin 13) (k : Fin 4) (r : Fin 22) :
    NormalizedQuerySection.evaluate (fun i => columns t ht j (i,k)) (t r) = 0 :=
  quotient_root t ht _ _ _ _ _

theorem columns_fold_zero (t : Fin 22 → QM31Exact) (ht : Function.Injective t)
    (j : Fin 13) (i : Fin 32) :
    ∑ k : Fin 4, (embed 7)^k.val * columns t ht j (i,k) = 0 :=
  quotient_fold t ht _ _ _ _

#print axioms columns_high
#print axioms matrix_independent_of_roots
#print axioms det_ne_zero
#print axioms selected_residual_surjective
#print axioms columns_root_zero
#print axioms columns_fold_zero
end
end AspisR19.QM31NormalizedSection
