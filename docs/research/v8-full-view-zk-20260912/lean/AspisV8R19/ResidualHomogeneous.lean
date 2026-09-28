/- The actual chord scale affects every low residual entry exactly once. -/
import AspisV8R19.ResidualPolynomial
import AspisV8R17.NormalizedChord

namespace AspisR19.ResidualHomogeneous
open ResidualModel ResidualPins AspisV8R17
variable {F : Type*} [CommRing F]
noncomputable section

theorem chord_scale (half t a b c : F) (j r : Nat) :
    chordEntry half (t*a) (t*b) (t*c) j r=t*chordEntry half a b c j r := by
  unfold chordEntry
  split_ifs <;> ring

theorem point_scale (half t a b c : F) (z : Fin 10 → F) (which r : Nat) :
    pointWeight order inactive half (t*a) (t*b) (t*c) z which r=
      t*pointWeight order inactive half a b c z which r := by
  simp only [pointWeight,chord_scale,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem polynomial_scale (quarter t : F) (q w : Fin 108 → F) (k : Nat) :
    polyCoeff quarter q (fun j => t*w j) k=t*polyCoeff quarter q w k := by
  simp only [polyCoeff,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro block _
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  split_ifs <;> ring

theorem observation_scale (half quarter t a b c κ alpha : F)
    (z : Fin 10 → F) (p : Fin 23 → F) (row : Nat) (col : Fin 13) :
    observation order inactive half quarter (t*a) (t*b) (t*c) κ alpha z p row col=
      t*observation order inactive half quarter a b c κ alpha z p row col := by
  have h3 (x y z : F) : κ*(t*x)+κ^2*(t*y)+κ^3*(t*z)=t*(κ*x+κ^2*y+κ^3*z) := by ring
  have h2 (x y : F) : κ^2*(t*x)+κ^3*(t*y)=t*(κ^2*x+κ^3*y) := by ring
  unfold observation
  simp_rw [point_scale,h3,h2,polynomial_scale]
  split_ifs <;> try rfl
  · simp
  · simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r _
    ring

theorem determinant_scale (half quarter t a b c κ alpha : F)
    (z : Fin 10 → F) (p : Fin 23 → F) :
    (minor order inactive half quarter (t*a) (t*b) (t*c) κ alpha z p).det=
      t^13*(minor order inactive half quarter a b c κ alpha z p).det := by
  have hm : minor order inactive half quarter (t*a) (t*b) (t*c) κ alpha z p=
      t • minor order inactive half quarter a b c κ alpha z p := by
    ext i j
    exact observation_scale half quarter t a b c κ alpha z p (selectedRow i) j
  rw [hm,Matrix.det_smul]
  simp

theorem rational_determinant {K : Type*} [Field K] (half quarter κ alpha u v : K)
    (z : Fin 10 → K) (p : Fin 23 → K) (hu : 1+u^2≠0) (hv : 1+v^2≠0) :
    (minor order inactive half quarter
      (rationalX u*rationalY v-rationalY u*rationalX v)
      (rationalY u-rationalY v) (rationalX v-rationalX u) κ alpha z p).det=
      chordScale u v^13*
        (minor order inactive half quarter (1+u*v) (u*v-1) (-(u+v)) κ alpha z p).det := by
  obtain ⟨ha,hb,hc⟩ := rational_chord_normalization u v hu hv
  rw [ha,hb,hc,determinant_scale]

#print axioms chord_scale
#print axioms point_scale
#print axioms polynomial_scale
#print axioms observation_scale
#print axioms determinant_scale
#print axioms rational_determinant
end
end AspisR19.ResidualHomogeneous
