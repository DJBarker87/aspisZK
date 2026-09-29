/- Sparse algebraic specialization. This is not an accepted OOD transcript. -/
import AspisV8R19.ResidualPins
import AspisV8R19.RootCertificate
import AspisV8R19.HighRepairInvariant
import Mathlib.Tactic.FinCases

namespace AspisR19.SparseHighWitness
open ResidualModel ResidualPins RootCertificate HighRepairInvariant
noncomputable section
def z (i : Fin 10) : M := ([0,0,0,1,1,0,0,1,0,2] : List M).getD i.val 0
def ew (which r : Nat) : M :=
  let c := fun j => chordEntry half (7:M) 5 (-5) r j
  if which=0 then 2*c 101-c 100
  else if which=1 then -2*c 100+c 101+4*c 102-2*c 103
  else 2*c 105-c 104
def e (which : Nat) (i : Index 32) : M := ew which (4*i.1.val+i.2.val)

theorem code0 (j : Fin 111) : codeWeight order inactive (point z 0) j =
    (if j=100 then -1 else 0)+(if j=101 then 2 else 0) := by
  fin_cases j <;> decide
theorem code1 (j : Fin 111) : codeWeight order inactive (point z 1) j =
    (if j=100 then -2 else 0)+(if j=101 then 1 else 0)+
      (if j=102 then 4 else 0)+(if j=103 then -2 else 0) := by
  fin_cases j <;> decide
theorem code2 (j : Fin 111) : codeWeight order inactive (point z 2) j =
    (if j=104 then -1 else 0)+(if j=105 then 2 else 0) := by
  fin_cases j <;> decide

theorem point0_weight (r : Nat) : pointWeight order inactive half (7:M) 5 (-5) z 0 r = ew 0 r := by
  simp [pointWeight,code0,ew,ite_mul,add_mul,Finset.sum_add_distrib]
  ring
theorem point1_weight (r : Nat) : pointWeight order inactive half (7:M) 5 (-5) z 1 r = ew 1 r := by
  simp [pointWeight,code1,ew,ite_mul,add_mul,Finset.sum_add_distrib]
  ring
theorem point2_weight (r : Nat) : pointWeight order inactive half (7:M) 5 (-5) z 2 r = ew 2 r := by
  simp [pointWeight,code2,ew,ite_mul,add_mul,Finset.sum_add_distrib]
  ring

theorem low0 (r : Fin 88) : ew 0 r.val=0 := by fin_cases r <;> decide
theorem low1 (r : Fin 88) : ew 1 r.val=0 := by fin_cases r <;> decide
theorem low2 (r : Fin 88) : ew 2 r.val=0 := by fin_cases r <;> decide

def degree (j : Fin 13) : Fin 32 := ⟨if j.val<12 then 24+j.val/3 else 31,by split_ifs <;> omega⟩
def slot (j : Fin 13) : Fin 4 := ⟨if j.val<12 then j.val%3+1 else 3,by split_ifs <;> omega⟩
def wr (i : Index 32) : M := 5*e 0 i+5^2*e 1 i+5^3*e 2 i
def hg (r : Nat) : M := half^10*chordEntry half (7:M) 5 (-5) r 128
theorem low_hg (r : Fin 88) : hg r.val=0 := by fin_cases r <;> decide
def wg (i : Index 32) : M := 5^2*e 1 i+5^3*e 2 i+5*hg (4*i.1.val+i.2.val)
def observation (row : Nat) (j : Fin 13) : M :=
  if row<3 then e row (degree j,slot j)-7^(slot j).val*e row (degree j,0)
  else if row<10 then localCoeff (536870912:M) 7 (degree j) (slot j) wr (row-3)
  else localCoeff (536870912:M) 7 (degree j) (slot j) wg (row-10)
def matrix : Matrix (Fin 13) (Fin 13) M := fun i j => observation (selectedRow i) j

#print axioms code0
#print axioms code1
#print axioms code2
#print axioms point0_weight
#print axioms point1_weight
#print axioms point2_weight
#print axioms low0
#print axioms low1
#print axioms low2
#print axioms low_hg
end
end AspisR19.SparseHighWitness
