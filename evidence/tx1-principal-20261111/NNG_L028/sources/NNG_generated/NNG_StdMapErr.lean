import NNG_EmittedContext
import NMP_StdMapErr
set_option autoImplicit false
namespace AspisR1.NNG_StdMapErr
open Aeneas Aeneas.Std Result NNG_verify_finish
/-- Reuse the complete std map_err implementation, including callback failure
and divergence, rather than a success-only or payload-forgetting stub. -/
abbrev run := @NMP_StdMapErr.run
/-- The fresh emitted source callback maps EVERY terminal error to Public. -/
theorem public_error {H : Type} (d : aspis_core.digest.Digest32 H)
 (e : aspis_core.state_only_prefix.r0.Error) :
 r1_semantic.verify_finish.closure.Insts.CoreOpsFunctionFnOnceTupleErrorError.call_once d () e=
 .ok r1_wire.Error.Public := rfl
#print axioms public_error
end AspisR1.NNG_StdMapErr
