import R1Z.PV_OptB_PathPoles
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_OptB_PoleCoordinates
open R0P AspisR1.SpendRelation R1Z.BuilderSpendRelation R1J.SpendWitnessMap
open PV_OptB_PathPoles
variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K] [CharP K 2147483647]

def allowed (pub : Public M) (w : Wspend) (lam : K) (t : Fin 16 → M) (i : Fin 16) : Finset M :=
  Finset.univ.filter (fun z => phi lam w i z ∈ PoleMassR1.poleSet (trace pub w t) lam)

theorem contains (pub : Public M) (w : Wspend) (lam : K) (t : Fin 16 → M) (i : Fin 16) :
    t i ∈ allowed pub w lam t i := by
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,phi_mem pub w t lam i⟩

theorem bounded (pub : Public M) (w : Wspend) (lam : K) (nonzero : lam ≠ 0)
    (t : Fin 16 → M) (i : Fin 16) : (allowed pub w lam t i).card ≤ 4096 := by
  have image_card : ((allowed pub w lam t i).image (phi lam w i)).card =
      (allowed pub w lam t i).card :=
    Finset.card_image_of_injective _ (phi_injective lam w i nonzero)
  rw [← image_card]
  apply (Finset.card_le_card ?_).trans (PoleMassR1.poleSet_card_le_4096 (trace pub w t) lam)
  intro a ha
  obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp ha
  exact (Finset.mem_filter.mp hz).2

theorem equal_of_poleSet_equal (pub : Public M) (w : Wspend) (lam : K) (t u : Fin 16 → M)
    (same : PoleMassR1.poleSet (trace pub w t) lam = PoleMassR1.poleSet (trace pub w u) lam) :
    allowed pub w lam t = allowed pub w lam u := by
  funext i
  unfold allowed
  rw [same]

#print axioms contains
#print axioms bounded
#print axioms equal_of_poleSet_equal
end R1Z.PV_OptB_PoleCoordinates
