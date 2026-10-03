import AspisR515SharedGamma.SharedGammaDots
import AspisR517GammaTowerCoordinates.GammaTowerCoordinates

/-! Transport the reused natural-channel kernel identity into the actual
quadratic tower arithmetic. Native u64 wrapping, arrays and the complete
selected preparation execution remain source correspondence obligations. -/
set_option autoImplicit false
namespace AspisR518GammaKernelTower
open AspisR517GammaTowerCoordinates
open AspisV8.SharedGammaDots AspisV8.SemanticCarry
variable {R : Type*} [CommRing R]

theorem fromCoords_add (x y : Fin 4 → R) :
    fromCoords (x + y) = fromCoords x + fromCoords y := by
  rw [← fromCoords_coords (fromCoords x + fromCoords y), coords_add,
    coords_fromCoords, coords_fromCoords]

theorem fromCoords_mul (x y : Fin 4 → R) :
    fromCoords (towerMul x y) = fromCoords x * fromCoords y := by
  rw [← fromCoords_coords (fromCoords x * fromCoords y), coords_mul,
    coords_fromCoords, coords_fromCoords]

theorem fromCoords_fold (xs : List ((Fin 4 → R) × (Fin 4 → R)))
    (seed : Fin 4 → R) :
    fromCoords (xs.foldl (fun s xy => s + towerMul xy.1 xy.2) seed) =
      xs.foldl (fun s xy => s + fromCoords xy.1 * fromCoords xy.2) (fromCoords seed) := by
  induction xs generalizing seed with
  | nil => rfl
  | cons xy xs ih =>
    simp only [List.foldl_cons, ih, fromCoords_add, fromCoords_mul]

theorem fromCoords_cast_fold (xs : List (Q Nat × Q Nat))
    (seed : Q (ZMod AspisV8.AffinePrimal.p)) :
    fromCoords (xs.foldl
      (fun s xy => s + towerMul (castQ xy.1) (castQ xy.2)) seed) =
    xs.foldl (fun s xy => s + fromCoords (castQ xy.1) * fromCoords (castQ xy.2))
      (fromCoords seed) := by
  induction xs generalizing seed with
  | nil => rfl
  | cons xy xs ih =>
    simp only [List.foldl_cons, ih, fromCoords_add, fromCoords_mul]

theorem fromCoords_group_fold (groups : List (List (Q Nat × Q Nat)))
    (seed : Q (ZMod AspisV8.AffinePrimal.p)) :
    fromCoords (groups.foldl
      (fun s xs => xs.foldl (fun u xy => u + towerMul (castQ xy.1) (castQ xy.2)) s) seed) =
    groups.foldl
      (fun s xs => xs.foldl
        (fun u xy => u + fromCoords (castQ xy.1) * fromCoords (castQ xy.2)) s)
      (fromCoords seed) := by
  induction groups generalizing seed with
  | nil => rfl
  | cons xs groups ih =>
    simp only [List.foldl_cons, ih, fromCoords_cast_fold]

theorem decoded_kernel_identity (groups : List (List (Q Nat × Q Nat))) (seed : C Nat) :
    fromCoords (AspisV8.AffinePrimal.reconstruct
      (castC (groups.foldl (fun s xs => s + partialC (rawGroup xs)) seed))) =
    groups.foldl
      (fun s xs => xs.foldl
        (fun u xy => u + fromCoords (castQ xy.1) * fromCoords (castQ xy.2)) s)
      (fromCoords (AspisV8.AffinePrimal.reconstruct (castC seed))) := by
  rw [kernel_result, fromCoords_group_fold]

#print axioms fromCoords_add
#print axioms fromCoords_mul
#print axioms fromCoords_fold
#print axioms fromCoords_cast_fold
#print axioms fromCoords_group_fold
#print axioms decoded_kernel_identity
end AspisR518GammaKernelTower
