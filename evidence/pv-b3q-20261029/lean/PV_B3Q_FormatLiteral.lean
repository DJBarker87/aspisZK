import PV_B3P_ClosureLinks14227
namespace PV_B3Q_FormatLiteral
open Aeneas Aeneas.Std PV_B3P_Groups14227
set_option autoImplicit false
abbrev Output := Result (Aeneas.Std.core.result.Result Unit Unit × Unit)
def source_rejection (_value : Usize) (_formatter : Unit) : Output := .ok (.Err (),())
/-- Quoted value port of the inspected always-Ok formatter. This definition
intentionally does not import its axiom-bearing function as a proof premise. -/
def quoted_model (_value : Usize) (formatter : Unit) : Output := .ok (.Ok (),formatter)
theorem literal_instance_false :
    ¬ PV_B3P_Link_std_dependency_closure14 (fun _ : Unit => Usize → Unit → Output)
      (fun _ => source_rejection) (fun _ => quoted_model) := by
 intro binding
 have same := congrFun (congrFun (binding ()) 17#usize) ()
 have impossible : true = false := congrArg (fun observed : Output =>
   match observed with | .ok (.Err _,_) => true | _ => false) same
 exact Bool.noConfusion impossible
#print axioms literal_instance_false
end PV_B3Q_FormatLiteral
