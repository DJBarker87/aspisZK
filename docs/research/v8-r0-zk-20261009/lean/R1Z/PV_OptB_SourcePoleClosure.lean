import R1Z.PV_OptB_SourcePoleBoundary
set_option autoImplicit false
namespace R1Z.PV_OptB_SourcePoleClosure
open Aeneas Aeneas.Std Result ProverRwFull ProverRwRetryModel
variable [ExternalTypes] [ExternalFuns]

theorem pole_error {H T : Type} (hash : aspis_core.digest.Digest32 H)
    (commitment : host_semantic.Commitments T) (compiled : Compiled) (pub : Pub)
    (lam chi : aspis_core.field.QM31)
    (pole : host_semantic.no_pole compiled lam chi = .ok (.Ok false)) :
    host_semantic.build_with_material.closure.Insts.CoreOpsFunctionFnOncePairQM31QM31ResultVecQM31Error.call_once
      hash commitment (compiled,pub) (lam,chi) = .ok (.Err .ActivePole) := by
  simp only [host_semantic.build_with_material.closure.Insts.CoreOpsFunctionFnOncePairQM31QM31ResultVecQM31Error.call_once,
    Aeneas.Std.uncurry,pole,bind_tc_ok,core.result.Result.Insts.CoreOpsTry.branch,Bool.false_eq_true,if_false]

#print axioms pole_error
end R1Z.PV_OptB_SourcePoleClosure
