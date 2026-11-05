import NHY_ErrorFragments
set_option autoImplicit false
namespace NIJ_GuardPrefix
open Aeneas Aeneas.Std Result

def visit (offset : Nat) : List Bool → Bool × List Nat
 | [] => (true,[])
 | b::bs => if b then (false,[offset]) else
   let tail := visit (offset+1) bs
   (tail.1,offset::tail.2)

def count : List Bool → Nat
 | [] => 0
 | b::bs => if b then 1 else 1+count bs

theorem trace (tests : List Bool) (offset : Nat) :
 (visit offset tests).2=List.range' offset (count tests) := by
 induction tests generalizing offset with
 | nil => rfl
 | cons b bs ih =>
   cases b <;> simp only [visit,count,Bool.false_eq_true,ite_false,ite_true]
   · rw [ih];simp [List.range'_succ,Nat.add_comm]
   · rfl

theorem bound (tests : List Bool) : count tests ≤ tests.length := by
 induction tests with
 | nil => rfl
 | cons b bs ih => cases b <;> simp only [count,Bool.false_eq_true,ite_false,ite_true,List.length_cons] <;> omega

theorem result (tests : List Bool) (offset : Nat) :
 (visit offset tests).1=!(tests.contains true) := by
 induction tests generalizing offset with
 | nil => rfl
 | cons b bs ih => cases b <;> simp [visit,ih]

def program (tests : List Bool) : Result (core.result.Result Unit NGL_ErrorModel.PE) :=
 ok (if (visit 0 tests).1 then .Ok () else .Err .InvalidAccountData)

theorem first_error (tests : List Bool) :
 program tests=ok (if tests.contains true then .Err .InvalidAccountData else .Ok ()) := by
 unfold program
 rw [result]
 cases tests.contains true <;> rfl

#print axioms trace
#print axioms bound
#print axioms result
#print axioms first_error
end NIJ_GuardPrefix
