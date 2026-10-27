import T2Nat_FinishResult
import T2Nat_RoundCode
import Tx2I_Nonvacuity
set_option autoImplicit false
noncomputable section
namespace AspisR1.T2Nat_FinishNonvacuity
open Aeneas Aeneas.Std Result AspisR1Stage2 AspisR1Stage2.Stage2Finish

/-- Existing local primitive-owner interpretation produces a successful full
Result/log pair. This is a local inhabitant, not an accepted deployed SDK pair. -/
theorem success_log {H : Type} (D : aspis_core.digest.Digest32 H) (hash : H)
    (x : E) (p0 : verifier.Prepared) (a0 : verifier.Accumulator)
    (v : verifier.View) (before : CheckpointBytes5Effect.Log) :
    CheckpointBytes5Effect.run D hash
      (T2Nat_Silent.code (T2Nat_FinishResult.installed (Tx2I_Nonvacuity.leaves x) v
        {p0 with variant := .S2,alpha := Array.repeat 2#usize x}
        {a0 with rhs := x,next := 22#usize})) before = ok (.Ok (),before) :=
  T2Nat_FinishResult.accepted_effects D hash _ _ _ _
    (Tx2I_Nonvacuity.finish_success x p0 a0 v) before

/-- Expanding a source round into all its arithmetic steps gives the same
full Result and ordered log as the parent's round leaf. No oracle event is
lost by the syntactic fission. -/
theorem round_fission {W H : Type} (D : aspis_core.digest.Digest32 H) (hash : H)
    (ops : FinishOps W) (poly : Slice U8) (alpha claim : E) (r : Usize)
    (before : CheckpointBytes5Effect.Log) :
    CheckpointBytes5Effect.run D hash
      (T2Nat_Silent.code (T2Nat_RoundCode.round ops poly alpha claim r)) before =
    CheckpointBytes5Effect.run D hash
      (T2Nat_Silent.code (T2Nat_Silent.call (Port4D_Round.round ops poly alpha claim r))) before := by
  rw [T2Nat_RoundCode.round_effects,T2Nat_Silent.ordered_log,T2Nat_Silent.erase_call]

#print axioms success_log
#print axioms round_fission
end AspisR1.T2Nat_FinishNonvacuity
end
