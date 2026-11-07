import NNG_Standard136
import NNG_DProjection136
import NNG_EmittedCallGraph
set_option autoImplicit false
namespace AspisR1.NNG_DPublicMap136
open Aeneas Aeneas.Std Result NNG_verify_finish NNG_Emitted NNG_EmittedCallGraph
open NNG_DProjection136

def qReply {VL : RSL.VLib} {H : Type} (p : Representation VL H) :
    core.result.Result Q r1_wire.Error → Except VL.WErr VL.QM31
  | .Ok q => .ok (p.q q)
  | .Err e => .error (p.error e)

/-- Full actual source map_err, after its actual closure: every terminal
error becomes Public; no callback failure or successful child is assumed. -/
theorem source {H : Type} (d : aspis_core.digest.Digest32 H)
    (r : core.result.Result Q aspis_core.state_only_prefix.r0.Error) :
    NNG_StdMapErr.run
      (r1_semantic.verify_finish.closure.Insts.CoreOpsFunctionFnOnceTupleErrorError d) r () =
    .ok (match r with | .Ok q => .Ok q | .Err _ => .Err r1_wire.Error.Public) := by
  cases r <;> rfl
#print axioms source

theorem projected {VL : RSL.VLib} {H : Type} (p : Representation VL H)
    (d : aspis_core.digest.Digest32 H) (r : core.result.Result Q aspis_core.state_only_prefix.r0.Error) :
    resultMap (qReply p) (NNG_StdMapErr.run
      (r1_semantic.verify_finish.closure.Insts.CoreOpsFunctionFnOnceTupleErrorError d) r ()) =
      .ok (RSL.RE.mapE (fun _ => VL.wPublic) (terminalReply p r)) := by
  rw [source]
  cases r with
  | Ok q => rfl
  | Err e => simp only [resultMap,qReply,terminalReply,RSL.RE.mapE,p.publicError]
#print axioms projected
end AspisR1.NNG_DPublicMap136
