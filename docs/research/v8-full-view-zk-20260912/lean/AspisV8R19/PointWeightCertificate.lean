/- Factor concrete point-weight evaluation into independently checked stages. -/
import AspisV8R19.RootCertificate
import AspisV8R19.ResidualPins

namespace AspisR19.PointWeightCertificate
open ResidualModel RootCertificate
variable {F : Type*} [CommRing F]
noncomputable section

def vector {n : Nat} (v : List Nat) (j : Fin n) : M := (v.getD j.val 0 : M)

theorem sparse_sum {n : Nat} (w e : Fin n → F) (s : Finset (Fin n))
    (hz : ∀ j, j ∉ s → e j = 0) :
    (∑ j, w j * e j) = ∑ j ∈ s, w j * e j := by
  symm
  apply Finset.sum_subset (Finset.subset_univ s)
  intro j _ hj
  rw [hz j hj, mul_zero]

theorem point_weight_stages (order : Fin 111 → Nat) (inactive : Fin 111 → Bool)
    (half a b c : F) (z coords : Fin 10 → F) (which : Nat)
    (code : Fin 111 → F) (out : Fin 108 → F)
    (hp : point z which = coords)
    (hc : codeWeight order inactive coords = code)
    (hw : ∀ r, (∑ j : Fin 111, code j * chordEntry half a b c r.val j.val) = out r) :
    ∀ r, pointWeight order inactive half a b c z which r.val = out r := by
  intro r
  unfold pointWeight
  rw [hp, hc]
  exact hw r

#print axioms point_weight_stages
#print axioms sparse_sum
end
end AspisR19.PointWeightCertificate
