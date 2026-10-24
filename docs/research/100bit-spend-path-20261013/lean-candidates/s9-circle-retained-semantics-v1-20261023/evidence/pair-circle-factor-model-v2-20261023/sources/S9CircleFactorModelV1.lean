import S9FactorTableSemanticsV1
import S9ConstructorV3DoubleRetainedModelV1

set_option autoImplicit false
namespace AspisR1S9CircleFactorModelV1
open AspisR1S9FactorTableSemanticsV1 AspisCircleTensorBinding

def base (x : ExactQM) (d : Nat) : ExactQM := doubledFactor x (2*d-1)

def coefficient (x : ExactQM) (d i : Nat) : ExactQM :=
  if i=0 then 1 else if i=1 then base x d else if i=2 then
    doubledFactor (base x d) 1 else base x d * doubledFactor (base x d) 1

def prefixTable (before : Table) (row start stop : Nat) (x : ExactQM) : Table :=
  fun k d i => if k=row ∧ start≤d ∧ d<stop then coefficient x d i else before k d i

theorem prefix_empty (before : Table) (row start : Nat) (x : ExactQM) :
    prefixTable before row start start x = before := by
  funext k d i
  have hn : ¬(k=row ∧ start≤d ∧ d<start) := by omega
  simp only [prefixTable,if_neg hn]

theorem prefix_step (before : Table) (row start stop : Nat) (x : ExactQM)
    (h : start≤stop) :
    write (prefixTable before row start stop x) row stop (coefficient x stop) =
      prefixTable before row start (stop+1) x := by
  funext k d i
  by_cases hk : k=row
  · by_cases hd : d=stop
    · subst k
      subst d
      simp [write,prefixTable,h]
    · have he : (start≤d ∧ d<stop+1) ↔ (start≤d ∧ d<stop) := by omega
      simp only [write,if_pos hk,if_neg hd,prefixTable,hk,true_and]
      rw [propext he]
  · have hn : ¬(k=row ∧ start≤d ∧ d<stop) := by omega
    have hn' : ¬(k=row ∧ start≤d ∧ d<stop+1) := by omega
    simp only [write,if_neg hk,prefixTable,if_neg hn,if_neg hn']

/-- Symbolic model transition; recurrence indices are manipulated without
expanding the repeated doubling expression. -/
theorem base_step_one (x : ExactQM) (d : Nat) (hd : 1≤d) :
    doubledFactor (base x d) 1 = doubledFactor x (2*d) := by
  unfold base
  rw [←AspisV5FriNaturalBasisRadix4.doubledFactor_add]
  congr 1
  omega

theorem base_step_two (x : ExactQM) (d : Nat) (hd : 1≤d) :
    doubledFactor (base x d) 2 = base x (d+1) := by
  unfold base
  rw [←AspisV5FriNaturalBasisRadix4.doubledFactor_add]
  congr 1
  omega

#print axioms prefix_empty
#print axioms prefix_step
#print axioms base_step_one
#print axioms base_step_two
end AspisR1S9CircleFactorModelV1
