import AspisV8R19.FullWitnessPointCode

/-! Exact-field v6_statement_points, including the special last-coordinate
initialization and the descending carry updates. Ten symbolic factors only. -/
namespace AspisR19.SourceStatementPoints
noncomputable section
variable {F : Type*} [CommRing F]

def reverseCoordinates : List (Fin 10) := [8,7,6,5,4,3,2,1,0]

theorem coordinates_eq : reverseCoordinates=
    ((List.finRange 9).reverse.map (fun i => (⟨i.val,by omega⟩ : Fin 10))) := by decide

def step (z : Fin 10 → F) (state : F × (Fin 10 → F)) (i : Fin 10) : F × (Fin 10 → F) :=
  let bc := z i*state.1
  (bc,Function.update state.2 i (z i+state.1-(bc+bc)))

def successor (z : Fin 10 → F) : Fin 10 → F :=
  (reverseCoordinates.foldl (step z) (z 9,Function.update z 9 (1-z 9))).2

theorem successor_eq (z : Fin 10 → F) (i : Fin 10) :
    successor z i=ResidualModel.point z 1 i := by
  fin_cases i <;>
    simp [successor,reverseCoordinates,step,ResidualModel.point,ResidualModel.carry,Fin.prod_univ_succ] <;> ring

def xor12 (z : Fin 10 → F) : Fin 10 → F :=
  ([7,6] : List (Fin 10)).foldl (fun out i => Function.update out i (1-out i)) z

theorem xor12_eq (z : Fin 10 → F) (i : Fin 10) : xor12 z i=ResidualModel.point z 2 i := by
  fin_cases i <;> simp [xor12,ResidualModel.point]

def points (z : Fin 10 → F) (which : Fin 3) : Fin 10 → F :=
  if which=0 then z else if which=1 then successor z else xor12 z

theorem points_eq (z : Fin 10 → F) (which : Fin 3) :
    points z which=ResidualModel.point z which.val := by
  funext i
  fin_cases which
  · simp [points,ResidualModel.point]
  · simpa [points] using successor_eq z i
  · simpa [points] using xor12_eq z i

#print axioms coordinates_eq
#print axioms successor_eq
#print axioms xor12_eq
#print axioms points_eq
end
end AspisR19.SourceStatementPoints
