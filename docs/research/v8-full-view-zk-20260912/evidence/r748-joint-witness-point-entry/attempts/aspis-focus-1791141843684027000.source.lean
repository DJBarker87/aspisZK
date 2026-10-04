import AspisV8R19.R748FiniteGatherSchedules
import AspisV8R19.R743JointSparseEntryBinding
open AspisV8R16 AspisV8R17 AspisR19
open AspisR19.TwoSwapSourceTable
open AspisV8R19.R740SparsePointObservation
open AspisV8R19.R743JointSparseEntryBinding
open AspisV8R19.R748FiniteGatherSchedules
open AspisR19.SourceStatementPoints
noncomputable section
namespace AspisV8R19.R748PointValueProbe
abbrev M := ZMod 2147483647
def z : Fin 10 → M := ![1,1,2,3,4,2,2,3,0,2]
def point := SourceStatementPoints.points z 1
def w (i : Nat) : M :=
  extendFin1024 (transportDual inactive 1023 order
    (fun j => sourcePointBasis point j.val)) i
#eval (List.map w [190,188,184,176,160,128,192,189,191, 0,2,4,1,3, 94,92,88,80,64,96,95,93,89,81,65,97])
#eval (List.map (fun n : Fin 1024 => (order n).val) ([190,188,184,176,160,128,192,189,191, 0,2,4,1,3, 94,92,88,80,64,96,95,93,89,81,65,97] : List (Fin 1024)))
#eval (List.map (sourceChordTranspose (1073741824 : M) w 7 5 (-5)) [191,188,3,0])
#eval sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 47 2 (.inr (.inl 1))
end AspisV8R19.R748PointValueProbe
namespace AspisV8R19.R748PointValueProbe
#eval (List.ofFn fun i : Fin 10 => point i)
#eval (List.map w [0,1,2,3,5,6,129,130,161,162,177,178,185,186,189,190,191,193,194,188])
#eval (List.map (fun n : Fin 1024 => (order n).val) ([0,1,2,3,5,6,129,130,161,162,177,178,185,186,189,190,191,193,194,188] : List (Fin 1024)))
#eval (List.map (fun n : Fin 1024 => isInactive (order n)) ([0,1,2,3,5,6,129,130,161,162,177,178,185,186,189,190,191,193,194,188] : List (Fin 1024)))
