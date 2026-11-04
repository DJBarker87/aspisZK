import PV_B3P_ExpandFrame592227
namespace PV_B3P_ExpandIndices592227
open Aeneas Aeneas.Std PV_B3P_PanicPatterns571227
set_option autoImplicit false
/-- Actual expand caller42:3859, scalar source189:29747. -/
theorem certificate_64_29747 {α : Type} (outer inner : Nat) (effects : List (Result Unit))
    (observed : IndexState)
    (ran : PV_B3P_ExpandEvents592227.sourceEvent .point 0 6 64 outer inner effects = .ok (some observed))
    (normal first second : Result α) :
    ¬ diagnostic (indexGuard observed) ∧
      branch (indexGuard observed) normal first = branch (indexGuard observed) normal second :=
  PV_B3P_ExpandEvents592227.event_certificate .point 0 6 64 outer inner effects observed ran normal first second
#print axioms certificate_64_29747
/-- Actual expand caller42:3859, scalar source189:29732. -/
theorem certificate_64_29732 {α : Type} (outer inner : Nat) (effects : List (Result Unit))
    (observed : IndexState)
    (ran : PV_B3P_ExpandEvents592227.sourceEvent .parent 0 6 64 outer inner effects = .ok (some observed))
    (normal first second : Result α) :
    ¬ diagnostic (indexGuard observed) ∧
      branch (indexGuard observed) normal first = branch (indexGuard observed) normal second :=
  PV_B3P_ExpandEvents592227.event_certificate .parent 0 6 64 outer inner effects observed ran normal first second
#print axioms certificate_64_29732
/-- Actual expand caller42:3859, scalar source189:29737. -/
theorem certificate_64_29737 {α : Type} (outer inner : Nat) (effects : List (Result Unit))
    (observed : IndexState)
    (ran : PV_B3P_ExpandEvents592227.sourceEvent .left 0 6 64 outer inner effects = .ok (some observed))
    (normal first second : Result α) :
    ¬ diagnostic (indexGuard observed) ∧
      branch (indexGuard observed) normal first = branch (indexGuard observed) normal second :=
  PV_B3P_ExpandEvents592227.event_certificate .left 0 6 64 outer inner effects observed ran normal first second
#print axioms certificate_64_29737
/-- Actual expand caller42:3859, scalar source189:29742. -/
theorem certificate_64_29742 {α : Type} (outer inner : Nat) (effects : List (Result Unit))
    (observed : IndexState)
    (ran : PV_B3P_ExpandEvents592227.sourceEvent .right 0 6 64 outer inner effects = .ok (some observed))
    (normal first second : Result α) :
    ¬ diagnostic (indexGuard observed) ∧
      branch (indexGuard observed) normal first = branch (indexGuard observed) normal second :=
  PV_B3P_ExpandEvents592227.event_certificate .right 0 6 64 outer inner effects observed ran normal first second
#print axioms certificate_64_29742
/-- Actual expand caller42:3866, scalar source189:29747. -/
theorem certificate_16_29747 {α : Type} (outer inner : Nat) (effects : List (Result Unit))
    (observed : IndexState)
    (ran : PV_B3P_ExpandEvents592227.sourceEvent .point 6 4 16 outer inner effects = .ok (some observed))
    (normal first second : Result α) :
    ¬ diagnostic (indexGuard observed) ∧
      branch (indexGuard observed) normal first = branch (indexGuard observed) normal second :=
  PV_B3P_ExpandEvents592227.event_certificate .point 6 4 16 outer inner effects observed ran normal first second
#print axioms certificate_16_29747
/-- Actual expand caller42:3866, scalar source189:29732. -/
theorem certificate_16_29732 {α : Type} (outer inner : Nat) (effects : List (Result Unit))
    (observed : IndexState)
    (ran : PV_B3P_ExpandEvents592227.sourceEvent .parent 6 4 16 outer inner effects = .ok (some observed))
    (normal first second : Result α) :
    ¬ diagnostic (indexGuard observed) ∧
      branch (indexGuard observed) normal first = branch (indexGuard observed) normal second :=
  PV_B3P_ExpandEvents592227.event_certificate .parent 6 4 16 outer inner effects observed ran normal first second
#print axioms certificate_16_29732
/-- Actual expand caller42:3866, scalar source189:29737. -/
theorem certificate_16_29737 {α : Type} (outer inner : Nat) (effects : List (Result Unit))
    (observed : IndexState)
    (ran : PV_B3P_ExpandEvents592227.sourceEvent .left 6 4 16 outer inner effects = .ok (some observed))
    (normal first second : Result α) :
    ¬ diagnostic (indexGuard observed) ∧
      branch (indexGuard observed) normal first = branch (indexGuard observed) normal second :=
  PV_B3P_ExpandEvents592227.event_certificate .left 6 4 16 outer inner effects observed ran normal first second
#print axioms certificate_16_29737
/-- Actual expand caller42:3866, scalar source189:29742. -/
theorem certificate_16_29742 {α : Type} (outer inner : Nat) (effects : List (Result Unit))
    (observed : IndexState)
    (ran : PV_B3P_ExpandEvents592227.sourceEvent .right 6 4 16 outer inner effects = .ok (some observed))
    (normal first second : Result α) :
    ¬ diagnostic (indexGuard observed) ∧
      branch (indexGuard observed) normal first = branch (indexGuard observed) normal second :=
  PV_B3P_ExpandEvents592227.event_certificate .right 6 4 16 outer inner effects observed ran normal first second
#print axioms certificate_16_29742
end PV_B3P_ExpandIndices592227
