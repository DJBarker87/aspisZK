import R1Z.PV_Inv_IInterpolationBasis
import R1Z.PV_Inv_IInterpolationPoly
/-! Derived into private PV_Inv module names for this focused proof; original theorem bodies retained.  Source descending update = multiplication by X-j. Sparsity is proved
symbolically and propagated; no concrete interpolation cell is evaluated. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_Inv_IBasisPolynomial
open Aeneas Aeneas.Std Result AspisR1ProducerRelease47
open ProverCommitM31Ops48 PV_Inv_IM31Array

def poly (xs : Nat → U32) : Polynomial M :=
  PV_Inv_IInterpolationPoly.poly 28 (fun k => decode (xs k))

theorem multiplication (xs : Nat → U32) (hxs : ∀ k, k < 28 → canonical (xs k))
    (j : U32) (n : Nat) (positive : 0 < n) (left : U8) (hleft : left.val=n) (bound : n ≤ 28)
    (space : ∀ k, k < 28 → n-1 ≤ k → decode (xs k)=0) :
    ∃ ys : Nat → U32,
      basis_mul (array 28#usize xs) j left=ok (array 28#usize ys) ∧
      (∀ k, k < 28 → canonical (ys k)) ∧
      poly ys=(Polynomial.X-Polynomial.C (decode j))*poly xs ∧
      ∀ k, k < 28 → n ≤ k → decode (ys k)=0 := by
  obtain ⟨ys,hy,hcy,hval⟩ := PV_Inv_IInterpolationBasis.basis_value xs hxs j n left hleft bound
  have hg : ∀ k, k < 28 → decode (ys k)=
      (if k=0 then 0 else decode (xs (k-1)))-decode (xs k)*decode j := by
    intro k hk
    rw [hval k hk]
    by_cases ht : k < n
    · rw [if_pos ht]
      rfl
    · rw [if_neg ht]
      have hk0 : k≠0 := by omega
      have hprev : k-1 < 28 := by omega
      have hz := space k hk (by omega)
      have hp := space (k-1) hprev (by omega)
      rw [if_neg hk0,hz,hp]
      simp only [zero_mul,sub_zero]
  refine ⟨ys,hy,hcy,?_,?_⟩
  · exact PV_Inv_IInterpolationPoly.mul_shape 28 (by decide)
      (fun k => decode (xs k)) (fun k => decode (ys k)) (decode j)
      (space 27 (by decide) (by omega)) hg
  · intro k hk hkn
    rw [hval k hk,if_neg (by omega)]
    exact space k hk (by omega)

#print axioms multiplication
end R1Z.PV_Inv_IBasisPolynomial
