import AspisR515SharedGamma.SemanticCarry
import AspisV8R17.QuadraticTowerOperations

namespace AspisR517GammaTowerCoordinates

namespace QTO := AspisV8R17.QuadraticTowerOperations
namespace SC := AspisV8.SemanticCarry

variable {R : Type*} [CommRing R]

abbrev TowerQ (R : Type*) [CommRing R] := QTO.Q R

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
    coords (x * y) = SC.towerMul (coords x) (coords y) := by
  rw [← QTO.qmul_eq]
  funext i
  fin_cases i <;>
    simp [coords, QTO.qmul, QTO.cmul, QTO.cr, QTO.r, SC.towerMul] <;> ring

#print axioms coords_fromCoords
#print axioms fromCoords_coords
#print axioms coords_add
#print axioms coords_mul

end AspisR517GammaTowerCoordinates
