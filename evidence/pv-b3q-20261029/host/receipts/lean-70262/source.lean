import PV_B3P_ClosureLinks14227
namespace PV_B3Q_FormatCounterexample
open Aeneas Aeneas.Std PV_B3P_Groups14227
set_option autoImplicit false
/-- Result port of Display<usize> when its underlying writer rejects the first
write. The callback is explicit; no writer failure is placed in T. -/
def rejecting_source (error : core.fmt.Error) (_value : Usize) (formatter : core.fmt.Formatter) :
    Result (core.result.Result Unit core.fmt.Error × core.fmt.Formatter) :=
 .ok (.Err error,formatter)
/-- The pinned no-op Display model cannot cover every source formatter. This
refutes this proposed generic instance, not op227's guarded callback theorem.
A certified panic-path exclusion or a faithful formatting model is required. -/
theorem rejecting_instance_false (error : core.fmt.Error) :
    ¬ PV_B3P_Link_std_dependency_closure14
      (fun _ : Unit => Usize → core.fmt.Formatter →
        Result (core.result.Result Unit core.fmt.Error × core.fmt.Formatter))
      (fun _ => rejecting_source error) (fun _ => core.fmt.num.imp.DisplayUsize.fmt) := by
 intro binding
 have same := congrFun (congrFun (binding ()) 17#usize) ()
 rw [core.fmt.num.imp.DisplayUsize.fmt.eq_1] at same
 change Result.ok (core.result.Result.Err error,()) = Result.ok (core.result.Result.Ok (),()) at same
 cases same
#print core.fmt.Error
#print core.fmt.num.imp.DisplayUsize.fmt
#print axioms rejecting_instance_false
end PV_B3Q_FormatCounterexample
