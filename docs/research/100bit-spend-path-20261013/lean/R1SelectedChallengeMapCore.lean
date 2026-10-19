import R0C.ModuloField
import R0P.SemD2
set_option autoImplicit false
noncomputable section
namespace AspisR1.SelectedChallengeMap
open AspisV8R19.SourceDuplexStep AspisWideTower AspisCircleGroupOrder
open R0P.SemSource
def sigma (i : Nat) (s : State) : WideExact :=
  if i = 27 then R0C.ModuloField.gamma s
  else if i = 28 ∨ i = 29 ∨ i = 30 then R0C.ModuloField.ordinary s
  else if i = 31 then 0
  else semChal s

def rhoOf (x : WideExact) : AspisV8R15.ExactTowerBase.QM31Exact := x.re

theorem semantic_row (i : Nat) (hi : i < 25) (s : State) :
    sigma i s = semChal s := by
  have h27 : i ≠ 27 := by omega
  have hopen : ¬ (i = 28 ∨ i = 29 ∨ i = 30) := by omega
  have h31 : i ≠ 31 := by omega
  simp only [sigma, if_neg h27, if_neg hopen, if_neg h31]

#print axioms sigma
#print axioms rhoOf
#print axioms semantic_row
end AspisR1.SelectedChallengeMap
end
