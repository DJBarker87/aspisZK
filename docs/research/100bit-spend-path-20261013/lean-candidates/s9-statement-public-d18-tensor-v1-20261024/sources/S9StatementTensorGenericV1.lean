import R1D18PointWeights
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace AspisR1S9StatementTensorGenericV1
variable {K : Type} [Field K]

def tensorRow (row : Nat → Nat → K) (j : Fin 1024) : K :=
  ∏ d : Fin 5,row d.val ((j.val/4^d.val)%4)

def pointFactor (p : Fin 10 → K) (d : Fin 5) (s : Nat) : K :=
  AspisR1.pairFactor
    (p ⟨9-2*(AspisR1.d18Tau d).val,by have := (AspisR1.d18Tau d).isLt;omega⟩)
    (p ⟨8-2*(AspisR1.d18Tau d).val,by have := (AspisR1.d18Tau d).isLt;omega⟩) s

/-- Five symbolic table factors give the retained D18 tensor functional;
no source row or1024-cell vector is expanded. -/
theorem tensorRow_eq_tensorPoint (row : Nat → Nat → K) (p : Fin 10 → K)
    (hf : ∀ (d : Fin 5) (s : Fin 4),row d.val s.val=pointFactor p d s.val)
    (j : Fin 1024) : tensorRow row j=AspisR1.tensorPoint p j := by
  unfold tensorRow AspisR1.tensorPoint
  apply Finset.prod_congr rfl
  intro d _
  exact hf d ⟨(j.val/4^d.val)%4,Nat.mod_lt _ (by omega)⟩

/-- Reuses the existing binary-row/radix-four theorem unchanged. -/
theorem tensorRow_eq_rowPoint (row : Nat → Nat → K) (p : Fin 10 → K)
    (hf : ∀ (d : Fin 5) (s : Fin 4),row d.val s.val=pointFactor p d s.val)
    (j : Fin 1024) : tensorRow row j=AspisR1.rowPoint p j :=
  (tensorRow_eq_tensorPoint row p hf j).trans (AspisR1.rowPoint_eq_tensorPoint p j).symm

#print axioms tensorRow_eq_tensorPoint
#print axioms tensorRow_eq_rowPoint
end AspisR1S9StatementTensorGenericV1
end
