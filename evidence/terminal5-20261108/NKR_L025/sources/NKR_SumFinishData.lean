import NJB_PatternReference
import NJL_EndpointIndices
set_option autoImplicit false
noncomputable section
namespace AspisR1.NKR_SumFinishData
/-- Frozen copy-terminal.rs tables546..575. Group batches are the actual
while-loop partition for group offsets0,9,15,26,30. -/
def group : Fin 30 → Fin 4 := ![0,0,0,0,0,0,0,0,0,1,1,1,1,1,1,2,2,2,2,2,2,2,2,2,2,2,3,3,3,3]
def low : Fin 30 → Fin 16 := ![0,1,2,4,6,10,11,12,14,2,6,10,11,12,14,0,1,2,4,5,6,7,9,10,12,13,6,7,9,12]
def offsets : Fin 5 → Nat := ![0,9,15,26,30]
def pLow : Fin 43 → Fin 16 := ![11,2,6,10,11,12,14,12,12,1,12,0,2,4,6,0,10,11,12,2,6,10,14,0,12,12,6,0,2,4,7,0,9,10,1,5,9,13,12,12,7,9,6]
def pOut : Fin 43 → Fin 26 := ![0,1,1,1,1,1,1,2,3,4,4,5,5,5,6,7,8,9,10,11,11,11,11,11,12,13,14,15,16,16,16,17,18,19,19,20,20,20,20,21,22,23,24,25]
def batchGroup : Fin 9 → Fin 4 := ![0,0,0,1,1,2,2,2,3]
def batchStart : Fin 9 → Nat := ![0,4,8,9,13,15,19,23,26]
def batchCount : Fin 9 → Nat := ![4,4,1,4,2,4,4,3,4]

theorem batch_domain (b : Fin 9) :
 1≤batchCount b ∧ batchCount b≤4 ∧ batchStart b+batchCount b≤30 ∧
 batchCount b=min 4 (offsets (batchGroup b).succ-batchStart b) := by
 fin_cases b <;> decide

def batchCoordinate (b : Fin 9) (i : Fin (batchCount b)) : Fin 30 :=
 ⟨batchStart b+i.val,by have h:=(batch_domain b).2.2.1;have:=i.isLt;omega⟩

theorem batch_same_group (b : Fin 9) (i : Fin (batchCount b)) :
 group (batchCoordinate b i)=batchGroup b := by
 fin_cases b <;> fin_cases i <;> rfl

theorem batch_interval (b : Fin 9) :
 offsets (batchGroup b).castSucc≤batchStart b ∧
 batchStart b<offsets (batchGroup b).succ := by
 fin_cases b <;> decide

/-- Actual per-group source chunk order, no whole-buffer native replay. -/
def batches : Fin 4 → List (Fin 9) := ![[0,1,2],[3,4],[5,6,7],[8]]

theorem batch_group (g : Fin 4) (b : Fin 9) (hb : b∈batches g) : batchGroup b=g := by
 fin_cases g <;> fin_cases b <;> simp [batches,batchGroup] at hb ⊢

#print axioms batch_domain
#print axioms batch_same_group
#print axioms batch_interval
#print axioms batch_group
end AspisR1.NKR_SumFinishData
end
