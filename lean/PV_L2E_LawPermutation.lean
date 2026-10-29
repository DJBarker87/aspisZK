import R0Z.AffineLaw
import Mathlib.Logic.Equiv.Sum
set_option autoImplicit false
noncomputable section
namespace PV_L2E_LawPermutation
attribute [local instance] Classical.propDecidable

/-- Equal finite laws on the SAME coin carrier give equal fibre cardinalities.
No output space is enumerated and no giant finite tape is normalized. -/
theorem fibre_card {R V : Type} [Fintype R] [Nonempty R]
    (f g : R → V) (h : R0Z.EqualLaws f g) (v : V) :
    Fintype.card {r // f r=v}=Fintype.card {r // g r=v} := by
  classical
  have hh := h v
  rw [R0Z.AffineLaw.law_eq_fibre_card,R0Z.AffineLaw.law_eq_fibre_card] at hh
  have hn : (Fintype.card R : ℚ)≠0 := by exact_mod_cast Fintype.card_ne_zero
  have hc := (div_left_inj' hn).mp hh
  exact_mod_cast hc

/-- A pointwise coupling chosen separately inside each output fibre. This
is not equality at identical tapes, and not a native state association. -/
def permutation {R V : Type} [Fintype R] [Nonempty R]
    (f g : R → V) (h : R0Z.EqualLaws f g) : R ≃ R := by
  classical
  exact (Equiv.sigmaFiberEquiv f).symm.trans
    ((Equiv.sigmaCongrRight (fun v => Fintype.equivOfCardEq (fibre_card f g h v))).trans
      (Equiv.sigmaFiberEquiv g))

theorem pointwise {R V : Type} [Fintype R] [Nonempty R]
    (f g : R → V) (h : R0Z.EqualLaws f g) (r : R) :
    g (permutation f g h r)=f r := by
  classical
  exact (Fintype.equivOfCardEq (fibre_card f g h (f r)) ⟨r,rfl⟩).property

/-- Coin-indexed tape relabelling leaves ALL middle coins unchanged. -/
def triangular {C R : Type} (e : C → R ≃ R) : (C × R) ≃ (C × R) where
  toFun p := (p.1,e p.1 p.2)
  invFun p := (p.1,(e p.1).symm p.2)
  left_inv p := by rcases p with ⟨c,r⟩; simp
  right_inv p := by rcases p with ⟨c,r⟩; simp

theorem retains_coins {C R : Type} (e : C → R ≃ R) (p : C × R) :
    (triangular e p).1=p.1 := rfl

#print axioms fibre_card
#print axioms permutation
#print axioms pointwise
#print axioms triangular
#print axioms retains_coins
end PV_L2E_LawPermutation
