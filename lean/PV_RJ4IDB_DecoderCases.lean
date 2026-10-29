import R1Z.PV_RJDec_TotalExtension
/-! Six clauses for each available decoder component under explicit lossless
state projection. Neither runtime observer nor its native binding is changed. -/
set_option autoImplicit false
namespace PV_RJ4IDB
open Aeneas Aeneas.Std R1Z.ProverCommitSemanticTransport26
variable {A B S T V O : Type}
def pullResult (project : A → B) (decode : Result B → V) (out : Result A) : V :=
 decode (mapR project out)

theorem disclosed_ok (project : S → T) (decode : Result (A × T) → V) (a : A) (s : S) :
 pullResult (fun p : A × S => (p.1,project p.2)) decode (.ok (a,s)) =
 decode (.ok (a,project s)) := rfl

theorem disclosed_fail (project : S → T) (decode : Result (A × T) → V) (e : Error) :
 pullResult (fun p : A × S => (p.1,project p.2)) decode (.fail e) = decode (.fail e) := rfl

theorem disclosed_div (project : S → T) (decode : Result (A × T) → V) :
 pullResult (fun p : A × S => (p.1,project p.2)) decode .div = decode .div := rfl

theorem oracle_ok (project : S → T) (decode : Result (A × T) → O) (a : A) (s : S) :
 pullResult (fun p : A × S => (p.1,project p.2)) decode (.ok (a,s)) =
 decode (.ok (a,project s)) := rfl

theorem oracle_fail (project : S → T) (decode : Result (A × T) → O) (e : Error) :
 pullResult (fun p : A × S => (p.1,project p.2)) decode (.fail e) = decode (.fail e) := rfl

theorem oracle_div (project : S → T) (decode : Result (A × T) → O) :
 pullResult (fun p : A × S => (p.1,project p.2)) decode .div = decode .div := rfl
#print axioms disclosed_ok
#print axioms disclosed_fail
#print axioms disclosed_div
#print axioms oracle_ok
#print axioms oracle_fail
#print axioms oracle_div
end PV_RJ4IDB
