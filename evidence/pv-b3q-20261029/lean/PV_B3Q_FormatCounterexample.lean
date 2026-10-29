import PV_B3P_ClosureLinks14227
namespace PV_B3Q_FormatCounterexample
open Aeneas Aeneas.Std PV_B3P_Groups14227
set_option autoImplicit false
/-- Result port of Display<usize> when its underlying writer rejects the first
write. The callback is explicit; no writer failure is placed in T. -/
def rejecting_source (error : Aeneas.Std.core.fmt.Error) (_value : Usize) (formatter : Aeneas.Std.core.fmt.Formatter) :
    Result (Aeneas.Std.core.result.Result Unit Aeneas.Std.core.fmt.Error × Aeneas.Std.core.fmt.Formatter) :=
 .ok (.Err error,formatter)
/-- The pinned no-op Display model cannot cover every source formatter. This
refutes this proposed generic instance, not op227's guarded callback theorem.
A certified panic-path exclusion or a faithful formatting model is required. -/
theorem rejecting_instance_false (error : Aeneas.Std.core.fmt.Error) :
    ¬ PV_B3P_Link_std_dependency_closure14
      (fun _ : Unit => Usize → Aeneas.Std.core.fmt.Formatter →
        Result (Aeneas.Std.core.result.Result Unit Aeneas.Std.core.fmt.Error × Aeneas.Std.core.fmt.Formatter))
      (fun _ => rejecting_source error) (fun _ => Aeneas.Std.core.fmt.num.imp.DisplayUsize.fmt) := by
 intro binding
 have same := congrFun (congrFun (binding ()) 17#usize) ()
 change rejecting_source error 17#usize () = Aeneas.Std.core.fmt.num.imp.DisplayUsize.fmt 17#usize () at same
 rw [Aeneas.Std.core.fmt.num.imp.DisplayUsize.fmt.eq_1] at same
 change Result.ok (Aeneas.Std.core.result.Result.Err error,()) = Result.ok (Aeneas.Std.core.result.Result.Ok (),()) at same
 cases same
#print Aeneas.Std.core.fmt.Formatter
#print Aeneas.Std.core.fmt.Error
#print Aeneas.Std.core.fmt.num.imp.DisplayUsize.fmt
theorem concrete_rejection :
    ¬ PV_B3P_Link_std_dependency_closure14
      (fun _ : Unit => Usize → Aeneas.Std.core.fmt.Formatter →
        Result (Aeneas.Std.core.result.Result Unit Aeneas.Std.core.fmt.Error × Aeneas.Std.core.fmt.Formatter))
      (fun _ => rejecting_source (() : Aeneas.Std.core.fmt.Error))
      (fun _ => Aeneas.Std.core.fmt.num.imp.DisplayUsize.fmt) := rejecting_instance_false ()
#print axioms rejecting_instance_false
#print axioms concrete_rejection
end PV_B3Q_FormatCounterexample
