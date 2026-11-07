import NNG_LIBScalar
import LIB_VCarriers
import NNG_EmittedContext
import NNG_Array136
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_LIBArrays
open Aeneas Aeneas.Std NNG_Emitted NNG_Transport
open AspisR1.NMT_Transport (arr arr_inverse)
open NNG_LIBScalar

def lowerArray {n : Usize} (a : Array Value n) : Array Raw n := arr lower a
def projectArray {n : Usize} (fallback : Value) (a : Array Raw n) : Array Value n := arr (project fallback) a

theorem project_lower_array {n : Usize} (fallback : Value) (a : Array Value n) :
    projectArray fallback (lowerArray a) = a :=
  arr_inverse lower (project fallback) (project_lower fallback) a
#print axioms project_lower_array

def lowerClaims (a : LIB_VCarriers.Claims) : Claims := arr lowerArray a
def projectClaims (fallback : Value) (a : Claims) : LIB_VCarriers.Claims := arr (projectArray fallback) a

theorem project_lower_claims (fallback : Value) (a : LIB_VCarriers.Claims) :
    projectClaims fallback (lowerClaims a) = a :=
  arr_inverse lowerArray (projectArray fallback) (project_lower_array fallback) a
#print axioms project_lower_claims

def lowerChallenges (a : LIB_VCarriers.Challenges) : NNG_verify_finish.aspis_core.state_only_prefix.r0.Challenges :=
  ⟨lower a.lambda,lower a.chi,lower a.theta,lowerArray a.zc,lower a.mu,lower a.eta⟩
def projectChallenges (fallback : Value) (a : NNG_verify_finish.aspis_core.state_only_prefix.r0.Challenges) : LIB_VCarriers.Challenges :=
  ⟨project fallback a.lambda,project fallback a.chi,project fallback a.theta,
   projectArray fallback a.zc,project fallback a.mu,project fallback a.eta⟩

theorem project_lower_challenges (fallback : Value) (a : LIB_VCarriers.Challenges) :
    projectChallenges fallback (lowerChallenges a) = a := by
  cases a
  simp only [projectChallenges,lowerChallenges,project_lower,project_lower_array]
#print axioms project_lower_challenges

theorem eta_input (fallback : Value) (a : LIB_VCarriers.Challenges) :
    LIB_VCarriers.eta a = project fallback (lowerChallenges a).eta :=
  (project_lower fallback a.eta).symm
#print axioms eta_input

/-- at28 commutes without assuming raw canonicality: the same total pointwise
projection is used by the source decoder and by the selected array field. -/
theorem at28 (fallback : Value) (a : K29) :
    LIB_VCarriers.at28 (projectArray fallback a) = project fallback (NNG_Array136.get a 28#usize (by decide)) := by
  unfold LIB_VCarriers.at28 projectArray NNG_Array136.get arr
  simp only [List.getElem_map]
  rfl
#print axioms at28
end AspisR1.NNG_LIBArrays
