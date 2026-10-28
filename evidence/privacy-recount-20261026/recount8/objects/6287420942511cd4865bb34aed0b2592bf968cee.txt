import R1Z.PV_RunJoin_SampleCanonical34
import R1Z.PV_RunJoin_WorkCoverage35
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_WorkCallback35
open Aeneas Aeneas.Std Result ProverRwFull
variable [ExternalTypes]

/-- All three actual callback entry points preserve the same argument index.
The FnMut writeback is the unchanged captured state, not a missing borrowed
array write. These are emitted callback laws, not native scheduling laws. -/
theorem call (ops : ExternalFuns) {H F : Type} (digest : aspis_core.digest.Digest32 H)
    (oracle : host_sumcheck.Oracle F) (c : host_sumcheck.prove_sumcheck_round.closure H F) (i : Usize) :
    (@host_sumcheck.prove_sumcheck_round.closure.Insts.CoreOpsFunctionFnTupleUsizeResultQM31Error _ ops H F digest oracle).call c i =
      @host_sumcheck.evaluate_assignment _ ops F oracle c.1 c.2.1 c.2.2.1 c.2.2.2 i := rfl

theorem call_mut (ops : ExternalFuns) {H F : Type} (digest : aspis_core.digest.Digest32 H)
    (oracle : host_sumcheck.Oracle F) (c : host_sumcheck.prove_sumcheck_round.closure H F) (i : Usize) :
    (@host_sumcheck.prove_sumcheck_round.closure.Insts.CoreOpsFunctionFnMutTupleUsizeResultQM31Error _ ops H F digest oracle).call_mut c i =
      (do let r ← @host_sumcheck.evaluate_assignment _ ops F oracle c.1 c.2.1 c.2.2.1 c.2.2.2 i
          .ok (r,c)) := rfl

theorem call_once (ops : ExternalFuns) {H F : Type} (digest : aspis_core.digest.Digest32 H)
    (oracle : host_sumcheck.Oracle F) (c : host_sumcheck.prove_sumcheck_round.closure H F) (i : Usize) :
    (@host_sumcheck.prove_sumcheck_round.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeResultQM31Error _ ops H F digest oracle).call_once c i =
      @host_sumcheck.evaluate_assignment _ ops F oracle c.1 c.2.1 c.2.2.1 c.2.2.2 i := by
  unfold host_sumcheck.prove_sumcheck_round.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeResultQM31Error
    host_sumcheck.prove_sumcheck_round.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeResultQM31Error.call_once
    host_sumcheck.prove_sumcheck_round.closure.Insts.CoreOpsFunctionFnMutTupleUsizeResultQM31Error.call_mut
    host_sumcheck.prove_sumcheck_round.closure.Insts.CoreOpsFunctionFnTupleUsizeResultQM31Error.call
  rcases c with ⟨f,p,r,a⟩
  simp only [bind_assoc_eq,bind_tc_ok]
  change (do let z ← @host_sumcheck.evaluate_assignment _ ops F oracle f p r a i
             .ok z) = _
  cases @host_sumcheck.evaluate_assignment _ ops F oracle f p r a i <;> rfl

#print axioms call
#print axioms call_mut
#print axioms call_once
end R1Z.PV_RunJoin_WorkCallback35
