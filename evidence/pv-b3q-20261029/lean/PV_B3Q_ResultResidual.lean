import PV_B3P_ClosureLinks14227
namespace PV_B3Q_ResultResidual
open Aeneas Aeneas.Std PV_B3P_Groups14227
set_option autoImplicit false
/-- The deployed result.rs from_residual: impossible Ok is eliminated, Err
calls From exactly once, preserving every Result tag from that conversion. -/
def source (T E F : Type) (convert : core.convert.From F E)
    (r : core.result.Result core.convert.Infallible E) : Result (core.result.Result T F) :=
 match r with
 | .Ok impossible => nomatch impossible
 | .Err e => do
   let converted ← convert.from e
   .ok (.Err converted)
def Signature (T E F : Type) : Unit → Type := fun _ =>
 core.convert.From F E → core.result.Result core.convert.Infallible E → Result (core.result.Result T F)
theorem residual_link (T E F : Type) : PV_B3P_Link_std_dependency_closure14
    (Signature T E F) (fun _ => source T E F)
    (fun _ => core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual T) := by
 intro _
 funext convert r
 cases r with
 | Ok impossible => cases impossible
 | Err e => rfl
/-- The Err source branch invokes conversion before constructing the new error;
there is no hidden catch, fallback value, or changed error carrier. -/
theorem conversion_failure (T E F : Type) (convert : core.convert.From F E) (e : E)
    (error : Aeneas.Std.Error) (failed : convert.from e = .fail error) :
    source T E F convert (.Err e) = .fail error := by
 simp only [source,failed,bind_tc_fail]
theorem conversion_divergence (T E F : Type) (convert : core.convert.From F E) (e : E)
    (diverged : convert.from e = .div) : source T E F convert (.Err e) = .div := by
 simp only [source,diverged,bind_tc_div]
#print axioms residual_link
#print axioms conversion_failure
#print axioms conversion_divergence
end PV_B3Q_ResultResidual
