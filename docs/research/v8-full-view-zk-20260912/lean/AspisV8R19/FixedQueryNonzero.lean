import AspisV8R19.FixedQueryDegree

namespace AspisR19.FixedQueryNonzero
open RootCertificate FixedQueryPolynomial
noncomputable section
variable {F : Type*} [Field F] [NeZero (2 : F)]

def assignment (f : M →+* F) (i : Fin 36) : F :=
  if h : i.val<10 then f (SparseHighWitness.z ⟨i.val,h⟩)
  else if i=10 then f 5 else if i=11 then f 7 else if i=12 then f 2 else if i=13 then f 3 else 0

theorem assignment_z (f : M →+* F) (i : Fin 10) :
    assignment f ⟨i.val,by omega⟩=f (SparseHighWitness.z i) := by
  simp [assignment,i.isLt]

theorem assigned_eq (f : M →+* F) (t : Fin 22 → F) (ht : Function.Injective t) :
    assigned (f half) (f 536870912) (FixedQuerySource.querySection t ht) (assignment f)=
      SourceFieldResidual.matrix f (fun _ => 0) 0 t := by
  have ha : 1+f 2*f 3=f 7 := by
    rw [← map_one f,← map_mul,← map_add]
    congr 1
  have hb : f 2*f 3-1=f 5 := by
    rw [← map_one f,← map_mul,← map_sub]
    congr 1
  have hc : -(f 2+f 3)=f (-5) := by
    rw [← map_add,← map_neg]
    congr 1
  unfold assigned normalizedMatrix
  simp only [assignment_z]
  rw [show assignment f 10=f 5 by simp [assignment],
    show assignment f 11=f 7 by simp [assignment],
    show assignment f 12=f 2 by simp [assignment],
    show assignment f 13=f 3 by simp [assignment],ha,hb,hc]
  rw [← FixedQuerySource.matrix_eq (f half) (f 536870912) (f 7) (f 5) (f (-5))
    (f 5) (f 7) 0 (fun i => f (SparseHighWitness.z i)) (fun _ => 0) t ht]
  rfl

theorem polynomial_ne_zero (f : M →+* F) (hf : Function.Injective f)
    (t : Fin 22 → F) (ht : Function.Injective t) :
    (polynomial (f half) (f 536870912) (FixedQuerySource.querySection t ht)).det≠0 := by
  intro hz
  have he := determinant_evaluation (f half) (f 536870912) (FixedQuerySource.querySection t ht) (assignment f)
  rw [hz,map_zero,assigned_eq] at he
  exact SourceFieldResidual.det_ne_zero f hf (fun _ => 0) 0 t ht he.symm

open AspisV8R15.ExactTowerBase QM31ResidualWitness
local instance : NeZero (2 : QM31Exact) := ⟨by
  intro h
  have hz : (2:M)=0 := embed_injective (by simpa only [map_ofNat,map_zero] using h)
  exact (by decide : (2:M)≠0) hz⟩

theorem exact_qm31 (t : Fin 22 → QM31Exact) (ht : Function.Injective t) :
    (polynomial (embed half) (embed 536870912) (FixedQuerySource.querySection t ht)).det≠0 ∧
      (polynomial (embed half) (embed 536870912) (FixedQuerySource.querySection t ht)).det.totalDegree≤819 :=
  ⟨polynomial_ne_zero embed embed_injective t ht,
    FixedQueryDegree.determinant_degree _ _ _⟩

#print axioms assignment_z
#print axioms assigned_eq
#print axioms polynomial_ne_zero
#print axioms exact_qm31
end
end AspisR19.FixedQueryNonzero
