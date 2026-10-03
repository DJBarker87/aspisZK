import AspisR515SharedGamma.SemanticCarry
import AspisV8R17.QuadraticTowerOperations

namespace AspisR517GammaTowerCoordinates

variable {R : Type*} [CommRing R]

abbrev TowerQ (R : Type*) [CommRing R] := AspisV8R17.QuadraticTowerOperations.Q R

def coords (x : TowerQ R) : Fin 4 → R := ![x.re.re, x.re.im, x.im.re, x.im.im]
def fromCoords (v : Fin 4 → R) : TowerQ R := ⟨⟨v 0, v 1⟩, ⟨v 2, v 3⟩⟩

theorem coords_fromCoords (v : Fin 4 → R) : coords (fromCoords v) = v := by
  funext i
  fin_cases i <;> simp [coords, fromCoords]

theorem fromCoords_coords (x : TowerQ R) : fromCoords (coords x) = x := by
  ext <;> simp [coords, fromCoords]

theorem coords_add (x y : TowerQ R) : coords (x + y) = coords x + coords y := by
  funext i
  fin_cases i <;> simp [coords]

theorem coords_mul (x y : TowerQ R) :
    coords (x * y) = AspisV8.SemanticCarry.towerMul (coords x) (coords y) := by
  rw [← AspisV8R17.QuadraticTowerOperations.qmul_eq]
  funext i
  fin_cases i <;>
    simp [coords, AspisV8R17.QuadraticTowerOperations.qmul, AspisV8R17.QuadraticTowerOperations.cmul, AspisV8R17.QuadraticTowerOperations.cr, AspisV8R17.QuadraticTowerOperations.r, AspisV8.SemanticCarry.towerMul] <;> ring

#print axioms coords_fromCoords
#print axioms fromCoords_coords
#print axioms coords_add
#print axioms coords_mul

end AspisR517GammaTowerCoordinates
