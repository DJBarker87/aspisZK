import R1Z.PV_RunJoin_RoundWorkerReached69
import R1Z.PV_RunJoin_RoundThread38
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_RoundSequencePlan72
open Aeneas Aeneas.Std Result ProverRwFull PV_RunJoin_Sequential64
open PV_RunJoin_RoundThread38 (Q Point Output)
variable [ExternalTypes] [ExternalFuns]

def round {H F A : Type} (digest : aspis_core.digest.Digest32 H) (oi : host_sumcheck.Oracle F)
    (transcript : host_wire.SemanticTranscript H) (output : alloc.vec.Vec U8)
    (point : Point) (running : Q) (r : Usize) (oracle : F) (next : Output H → Plan A) : Plan A :=
  let assignments := Usize.wrapping_shl 1#usize (UScalar.cast .U32 (Usize.wrapping_sub 9#usize r))
  .step aspis_core.field.QM31.ZERO (fun _ => .worker
    (host_sumcheck.prove_sumcheck_round.closure.Insts.CoreOpsFunctionFnTupleUsizeResultQM31Error digest oi)
    (Usize.wrapping_add 100#usize r) (Usize.wrapping_mul 28#usize assignments)
    (oracle,point,r,assignments)
    (fun evaluations => .step (PV_RunJoin_RoundWorkerReached69.tail digest transcript output point
      running r assignments evaluations) next))

theorem round_execute {H F A S E : Type} (runtime : PV_RunJoin_AllocatorWorld63.Runtime S E)
    (world : PV_FXM_ReserveWorld.World S E)
    (digest : aspis_core.digest.Digest32 H) (oi : host_sumcheck.Oracle F)
    (transcript : host_wire.SemanticTranscript H) (output : alloc.vec.Vec U8)
    (point : Point) (running : Q) (r : Usize) (oracle : F) (next : Output H → Plan A) :
    execute runtime (round digest oi transcript output point running r oracle next) world=
      (do let triple ← host_sumcheck.prove_sumcheck_round digest oi transcript output point running r oracle
          execute runtime (next triple) world) := by
  rw [PV_RunJoin_RoundWorkerReached69.reached]
  simp only [round,execute,bind_assoc_eq]

def phase {H F : Type} (digest : aspis_core.digest.Digest32 H) (oi : host_sumcheck.Oracle F) :
    Nat → host_wire.SemanticTranscript H → alloc.vec.Vec U8 → Point → Q → Usize → F → Plan (Output H)
  | 0,t,o,p,q,_,oracle => .step (PV_RunJoin_RoundThread38.finish oi t o p q oracle) Plan.done
  | n+1,t,o,p,q,r,oracle => round digest oi t o p q r oracle (fun (status,t',o') =>
      match status with
      | .Err e => .done (.Err e,t',o')
      | .Ok (p',q') => phase digest oi n t' o' p' q' (Usize.wrapping_add r 1#usize) oracle)

theorem phase_execute {H F S E : Type} (runtime : PV_RunJoin_AllocatorWorld63.Runtime S E)
    (world : PV_FXM_ReserveWorld.World S E)
    (digest : aspis_core.digest.Digest32 H) (oi : host_sumcheck.Oracle F)
    (n : Nat) (t : host_wire.SemanticTranscript H) (o : alloc.vec.Vec U8)
    (p : Point) (q : Q) (r : Usize) (oracle : F) :
    execute runtime (phase digest oi n t o p q r oracle) world=
      (do let triple ← PV_RunJoin_RoundThread38.phase digest oi n t o p q r oracle
          ok (triple,world)) := by
  induction n generalizing t o p q r with
  | zero => simp only [phase,execute,PV_RunJoin_RoundThread38.phase]
  | succ n ih =>
    rw [phase,round_execute]
    simp only [PV_RunJoin_RoundThread38.phase,bind_assoc_eq]
    apply congrArg (Aeneas.Std.bind (host_sumcheck.prove_sumcheck_round digest oi t o p q r oracle))
    funext triple
    rcases triple with ⟨status,t',o'⟩
    cases status with
    | Err e =>
      simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok,
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
        core.convert.FromSame,execute]
    | Ok pair =>
      rcases pair with ⟨p',q'⟩
      simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok,lift]
      exact ih t' o' p' q' (Usize.wrapping_add r 1#usize)

#print axioms round
#print axioms round_execute
#print axioms phase
#print axioms phase_execute
end R1Z.PV_RunJoin_RoundSequencePlan72
