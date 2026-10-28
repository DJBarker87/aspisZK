import NCE_OpeningRead
import NBI_Admission

set_option autoImplicit false
noncomputable section
namespace AspisR1.NCE_AdmissionCuts
open Aeneas Aeneas.Std NCE_OpeningCuts MultiproofConeCountPhysical
attribute [local instance] Classical.propDecidable

def index (s : Carrier) (i : Nat) : Nat := s.scratch.idx.val[i]!.val
abbrev Predicate := Carrier → Nat → Bool × Carrier

/-- ONE actual adjacent-window or range predicate on the SAME live backing.
No well-formed result or all-loop success is a hypothesis. Native iterator/
slice provenance and full all() control still need their source association. -/
def NCE_Native_Admission (pair range : Predicate) : Prop :=
  (∀ s i, s.scratch.n.val ≤ 16 → i+1 < s.scratch.n.val →
    pair s i = (decide (index s i < index s (i+1)),s)) ∧
  (∀ s i, s.scratch.n.val ≤ 16 → i < s.scratch.n.val →
    range s i = (decide (index s i < 262144),s))

def adjacent (pair : Predicate) : Nat → Nat → Carrier → Bool × Carrier
  | 0,_,s => (true,s)
  | fuel+1,i,s => let out := pair s i
                   if out.1 then adjacent pair fuel (i+1) out.2 else out

def ranged (range : Predicate) : Nat → Nat → Carrier → Bool × Carrier
  | 0,_,s => (true,s)
  | fuel+1,i,s => let out := range s i
                   if out.1 then ranged range fuel (i+1) out.2 else out

/-- Same-carrier adjacent scan from one-window cuts to the EXISTING NBI
predicate, including its first false branch. No Pairwise theorem is reproved. -/
theorem adjacent_eq (pair range : Predicate) (cut : NCE_Native_Admission pair range)
    (fuel i : Nat) (s : Carrier) (small : s.scratch.n.val ≤ 16)
    (span : i+fuel+1 ≤ s.scratch.n.val) :
    adjacent pair fuel i s = (NBI_Admission.adjacent (cells (index s) i (fuel+1)),s) := by
  induction fuel generalizing i with
  | zero => rfl
  | succ fuel ih =>
    have step : NBI_Admission.adjacent (cells (index s) i ((fuel+1)+1)) =
        (decide (index s i < index s (i+1)) &&
          NBI_Admission.adjacent (cells (index s) (i+1) (fuel+1))) := by
      rw [cells_cons (index s) i (fuel+1)]
      simp only [cells_cons,NBI_Admission.adjacent]
    rw [adjacent,cut.1 s i small (by omega)]
    simp only
    rw [step]
    by_cases ordered : index s i < index s (i+1)
    · simp only [ordered,decide_true,if_true,Bool.true_and]
      exact ih (i+1) (by omega)
    · simp only [ordered,decide_false,Bool.false_eq_true,if_false,Bool.false_and]

/-- Every range check consumes the predecessor's returned carrier. -/
theorem ranged_eq (pair range : Predicate) (cut : NCE_Native_Admission pair range)
    (fuel i : Nat) (s : Carrier) (small : s.scratch.n.val ≤ 16)
    (span : i+fuel ≤ s.scratch.n.val) :
    ranged range fuel i s = ((cells (index s) i fuel).all (fun k => decide (k < 262144)),s) := by
  induction fuel generalizing i with
  | zero => simp only [ranged,cells,List.range_zero,List.map_nil,List.all_nil]
  | succ fuel ih =>
    rw [ranged,cut.2 s i small (by omega)]
    simp only
    rw [cells_cons,List.all_cons]
    by_cases valid : index s i < 262144
    · simp only [valid,decide_true,if_true,Bool.true_and]
      exact ih (i+1) (by omega)
    · simp only [valid,decide_false,Bool.false_eq_true,if_false,Bool.false_and]

/-- Source-order well-formed predicates, preserving early failure and frame.
Native empty/length guards are consumed separately by the verifier PC cut. -/
def check (pair range : Predicate) (s : Carrier) : Bool × Carrier :=
  if s.scratch.n.val = 0 then (false,s) else
    let order := adjacent pair (s.scratch.n.val-1) 0 s
    if order.1 then ranged range s.scratch.n.val 0 order.2 else order

/-- Compute the existing admission from native one-window predicates. There
is no successful validation value premise; order/range may both reject. -/
theorem check_eq (pair range : Predicate) (cut : NCE_Native_Admission pair range)
    (s : Carrier) (small : s.scratch.n.val ≤ 16) :
    check pair range s = (NBI_Admission.admission (cells (index s) 0 s.scratch.n.val),s) := by
  by_cases empty : s.scratch.n.val = 0
  · simp only [check,if_pos empty,empty,cells,List.range_zero,List.map_nil,NBI_Admission.admission,
      List.isEmpty_nil,Bool.not_true,Bool.false_and,ite_true]
  · have positive : 0 < s.scratch.n.val := by omega
    have shape : s.scratch.n.val-1+1 = s.scratch.n.val := by omega
    rw [check,if_neg empty,adjacent_eq pair range cut _ _ s small (by omega)]
    simp only [shape]
    have nonempty : (cells (index s) 0 s.scratch.n.val).isEmpty = false := by
      rw [←shape,cells_cons]
      rfl
    have length : (cells (index s) 0 s.scratch.n.val).length = s.scratch.n.val := by
      simp only [cells,List.length_map,List.length_range]
    unfold NBI_Admission.admission
    rw [nonempty,length]
    simp only [small,decide_true,Bool.not_false,Bool.true_and]
    cases test : NBI_Admission.adjacent (cells (index s) 0 s.scratch.n.val) with
    | false => simp only [Bool.false_eq_true,if_false,Bool.false_and]
    | true =>
      simp only [if_true,Bool.true_and]
      exact ranged_eq pair range cut _ _ s small (by omega)

/-- The existing mathematical Pairwise/domain theorem is consumed once. -/
theorem check_iff (pair range : Predicate) (cut : NCE_Native_Admission pair range)
    (s : Carrier) (small : s.scratch.n.val ≤ 16) :
    (check pair range s).1 = true ↔
      OraclePortFrozenOrder.wellFormed (cells (index s) 0 s.scratch.n.val) := by
  rw [check_eq pair range cut s small]
  exact NBI_Admission.admission_iff _

#print axioms adjacent_eq
#print axioms ranged_eq
#print axioms check_eq
#print axioms check_iff
end AspisR1.NCE_AdmissionCuts
end
