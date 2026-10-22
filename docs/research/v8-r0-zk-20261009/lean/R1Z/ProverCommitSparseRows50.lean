import R1Z.ProverCommitSparse50
import R1Z.ProverCommitBooleanEnum49
import R0P.SemView
/-! Source MSB-first row weights are the existing model's eqWeight at toR0.
The result is an arbitrary row, not an expanded concrete cube. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverCommitSparseRows50
open scoped BigOperators
variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K]

def reverse : Fin 10 ≃ Fin 10 where
  toFun := fun i => ⟨9-i.val,by have := i.isLt;omega⟩
  invFun := fun i => ⟨9-i.val,by have := i.isLt;omega⟩
  left_inv := by intro i;apply Fin.ext;dsimp;have := i.isLt;omega
  right_inv := by intro i;apply Fin.ext;dsimp;have := i.isLt;omega

theorem row (p : Fin 10 → K) (a : Fin 1024) :
    ProverCommitSparse50.weight p (ProverCommitBooleanEnum49.tail 10 a)=
      AspisR0.Opening.eqWeight (R0P.SemSource.toR0 p) a := by
  unfold AspisR0.Opening.eqWeight
  rw [← Equiv.prod_comp reverse]
  unfold ProverCommitSparse50.weight
  apply Finset.prod_congr rfl
  intro i hi
  have hrev2 : 9-(9-i.val)=i.val := by have := i.isLt;omega
  change (if ProverCommitBooleanEnum49.tail 10 a i then p i else 1-p i)=
    (if a.val/2^(9-i.val)%2=0 then
      1-p ⟨9-(9-i.val),by have := i.isLt;omega⟩ else
      p ⟨9-(9-i.val),by have := i.isLt;omega⟩)
  have he : (⟨9-(9-i.val),by have := i.isLt;omega⟩ : Fin 10)=i := Fin.ext hrev2
  rw [he]
  rw [ProverCommitBooleanEnum49.tail,Nat.testBit_eq_decide_div_mod_eq]
  by_cases h : a.val/2^(9-i.val)%2=0
  · simp only [h,show (0:Nat)≠1 by decide,decide_false,Bool.false_eq_true,if_false,if_true]
  · have h1 : a.val/2^(9-i.val)%2=1 := by omega
    simp only [h1,decide_true,if_true,show (1:Nat)≠0 by decide,if_false]

#print axioms row
end R1Z.ProverCommitSparseRows50
