import RPu_FJd_LoopReference
import Mathlib.Algebra.BigOperators.Fin
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJd_HighReference
open scoped BigOperators
variable {K : Type} [Field K]
/-- Source shared path: 4 partials, each 16 entries, high factor last. -/
def shared (f : Fin 64 → K) (common : Fin 16 → K) (high : Fin 4 → K) : K :=
  ∑ s : Fin 4, (∑ j : Fin 16,
    f ⟨16*s.val+j.val,by have := s.isLt;have := j.isLt;omega⟩*common j)*high s

def index : (Fin 4 × Fin 16) ≃ Fin 64 where
  toFun x:=⟨16*x.1.val+x.2.val,by have := x.1.isLt;have := x.2.isLt;omega⟩
  invFun i:=(⟨i.val/16,by have := i.isLt;omega⟩,⟨i.val%16,Nat.mod_lt _ (by omega)⟩)
  left_inv x:=by
    apply Prod.ext
    · apply Fin.ext;dsimp;have hs:=x.1.isLt;have hj:=x.2.isLt;omega
    · apply Fin.ext;dsimp;have hs:=x.1.isLt;have hj:=x.2.isLt;omega
  right_inv i:=by apply Fin.ext;dsimp;omega

theorem value (f : Fin 64 → K) (common : Fin 16 → K) (high : Fin 4 → K) :
    shared f common high=
      ∑ i : Fin 64, f i*(common ⟨i.val%16,Nat.mod_lt _ (by omega)⟩*
        high ⟨i.val/16,by have := i.isLt;omega⟩) := by
  unfold shared
  simp_rw [Finset.sum_mul]
  have hs : (∑ s : Fin 4,∑ j : Fin 16, f (index (s,j))*common j*high s)=
      ∑ x : Fin 4 × Fin 16,f (index x)*common x.2*high x.1 := by
    rw [Fintype.sum_prod_type]
  change (∑ s : Fin 4,∑ j : Fin 16, f (index (s,j))*common j*high s)=_
  rw [hs]
  apply Fintype.sum_equiv index
  intro x
  dsimp [index]
  have h0 : (16*x.1.val+x.2.val)%16=x.2.val := by have := x.2.isLt;omega
  have h1 : (16*x.1.val+x.2.val)/16=x.1.val := by have := x.2.isLt;omega
  simp only [h0,h1]
  ring
#print axioms value
end AspisR1.FJd_HighReference
end
