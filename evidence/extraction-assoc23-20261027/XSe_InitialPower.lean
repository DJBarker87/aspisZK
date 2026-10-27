import XSe_PowerCanonical
import XRr_Initial64
open Aeneas Aeneas.Std Result XRn_Join_Release XRk_ResultTools
set_option autoImplicit false
namespace XSe_InitialPower
/-- Initial power canonicality is derived from THIS actual S2 constructor. -/
theorem source (a : verifier.Accumulator)
 (run : verifier.Accumulator.new .S2=ok (.Ok a)) : XRp_PowersQAdd.CanonicalQ a.power := by
 unfold verifier.Accumulator.new at run
 rw [XRr_Initial64.width,bind_tc_ok] at run
 obtain ⟨zero,_,run⟩ := bind_success _ _ _ run
 obtain ⟨r,_,run⟩ := bind_success _ _ _ run
 cases r with
 | Err e =>
   simp [core.result.Result.map_err,
    verifier.Accumulator.new.closure.Insts.CoreOpsFunctionFnOnceTupleErrorError.call_once,
    core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
    core.convert.FromSame.from] at run
 | Ok weights =>
   simp only [core.result.Result.map_err,bind_tc_ok,
    core.result.Result.Insts.CoreOpsTry.branch] at run
   obtain ⟨wide,_,run⟩ := bind_success _ _ _ run
   obtain ⟨one,hone,run⟩ := bind_success _ _ _ run
   unfold aspis_core.field.QM31.ONE at hone
   cases Result.ok.inj hone
   cases core.result.Result.Ok.inj (Result.ok.inj run)
   change ((1<2147483647 ∧ 0<2147483647) ∧ (0<2147483647 ∧ 0<2147483647))
   decide
#print axioms source
end XSe_InitialPower
