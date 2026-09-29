/- Functoriality of the restricted residual model, before any probability law. -/
import AspisV8R19.SourceResidualPolynomial

namespace AspisR19.ResidualFieldLift
open ResidualModel SourceResidualPolynomial
variable {F G : Type*} [CommRing F] [CommRing G]
noncomputable section

theorem map_assigned (f : F →+* G) (half quarter : F) (s : Fin 36 → F) :
    (assignedMinor half quarter s).map f =
      assignedMinor (f half) (f quarter) (fun i => f (s i)) := by
  ext i j
  unfold assignedMinor normalizedMinor minor
  simp only [Matrix.map_apply, map_observation, map_rootCoefficients,
    map_add, map_mul, map_sub, map_neg, map_one]

theorem map_assigned_det (f : F →+* G) (half quarter : F) (s : Fin 36 → F) :
    f (assignedMinor half quarter s).det =
      (assignedMinor (f half) (f quarter) (fun i => f (s i))).det := by
  rw [f.map_det]
  exact congrArg Matrix.det (map_assigned f half quarter s)

theorem assigned_det_ne_zero (f : F →+* G) (hf : Function.Injective f)
    (half quarter : F) (s : Fin 36 → F)
    (h : (assignedMinor half quarter s).det ≠ 0) :
    (assignedMinor (f half) (f quarter) (fun i => f (s i))).det ≠ 0 := by
  rw [← map_assigned_det]
  intro hz
  apply h
  apply hf
  simpa only [map_zero] using hz

#print axioms map_assigned
#print axioms map_assigned_det
#print axioms assigned_det_ne_zero
end
end AspisR19.ResidualFieldLift
