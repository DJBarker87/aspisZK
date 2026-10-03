import AspisR515SharedGamma.SemanticCarry
import AspisV8R17.QuadraticTowerOperations

namespace AspisR517GammaTowerCoordinates

open AspisV8R17.QuadraticTowerOperations
open AspisV8.SemanticCarry

variable {R : Type*} [CommRing R]

abbrev Q (R : Type*) [CommRing R] := QuadraticTowerOperations.Q R

def coords (x : Q R) : Fin 4 → R := ![x.re.re, x.re.im, x.im.re, x.im.im]
def fromCoords (v : Fin 4 → R) : Q R := ⟨⟨v 0, v 1⟩, ⟨v 2, v 3⟩⟩

theorem coords_fromCoords (v : Fin 4 → R) : coords (fromCoords v) = v := by
  funext i
  fin_cases i <;> rfl

theorem fromCoords_coords (x : Q R) : fromCoords (coords x) = x := by
  ext <;> rfl

theorem coords_add (x y : Q R) : coords (x + y) = coords x + coords y := by
  funext i
  fin_cases i <;> simp [coords]

theorem coords_mul (x y : Q R) :
    coords (x * y) = towerMul (coords x) (coords y) := by
  rw [← qmul_eq]
  funext i
  fin_cases i <;> simp [coords, qmul, cmul, cr, r, towerMul] <;> ring

#print axioms coords_fromCoords
#print axioms fromCoords_coords
#print axioms coords_add
#print axioms coords_mul

end AspisR517GammaTowerCoordinates
