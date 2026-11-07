import NHS_QueryFailures
import NGN_EmittedEq
set_option autoImplicit false
noncomputable section
namespace LIBC_PreparedErrors
open Aeneas Aeneas.Std Result AspisR1 AspisR1PublicPreparation
open NFW_PreparedControl NHL_PreparedScalars
/-- Fixed CLOSED boundary installation, not a free Ops parameter. This equality
includes both returned Errors, scratch writeback, fail and divergence. -/
theorem complete (D : aspis_core.Digest32 Unit) (sem : r1_semantic.Verified Unit)
 (v : verifier.View) (old : Scratch) :
 NGN_Emitted.prepared actual D sem v () old =
 PreparedScratchModel.prepare actual D sem v () old := NGN_EmittedEq.source actual D sem v () old
/-- F3: query errors precede scratch overwrite. No returned/success premise:
the conclusion inspects the entire actual child Result. -/
theorem query_nonok (D : aspis_core.Digest32 Unit) (sem : r1_semantic.Verified Unit)
 (v : verifier.View) (old : Scratch) (o : Opening Unit) :
 match actual.sampling.queries D o.transcript o.row v.final_message with
 | .ok (.Err e,_) => NGN_Cuts.queryCut actual D sem v old o = .ok (.Err e,old)
 | .fail e => NGN_Cuts.queryCut actual D sem v old o = .fail e
 | .div => NGN_Cuts.queryCut actual D sem v old o = .div
 | .ok (.Ok _,_) => True := by
 cases h : actual.sampling.queries D o.transcript o.row v.final_message with
 | fail e => simp only [NGN_Cuts.queryCut,h,bind_tc_fail]
 | div => simp only [NGN_Cuts.queryCut,h,bind_tc_div]
 | ok p =>
  rcases p with ⟨r,t⟩
  cases r with
  | Ok qs => trivial
  | Err e =>
   simp only [NGN_Cuts.queryCut,h,bind_tc_ok,core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
    core.convert.FromSame]
   rfl
/-- F3: a claim error follows the powers write. The produced g, rather than
incoming scratch, is retained on every returned claim Err. -/
theorem claim_nonok (D : aspis_core.Digest32 Unit) (sem : r1_semantic.Verified Unit)
 (v : verifier.View) (g : Scratch) (o : Opening Unit) (qs : Array U32 22#usize)
 (rho : aspis_core.field.QM31) (last : transcript.Transcript Unit) :
 match actual.claim D sem v.y1 v.inactive g o.kappa with
 | .ok (.Err e) => NGN_Cuts.claimCut actual D sem v g o qs rho last = .ok (.Err e,g)
 | .fail e => NGN_Cuts.claimCut actual D sem v g o qs rho last = .fail e
 | .div => NGN_Cuts.claimCut actual D sem v g o qs rho last = .div
 | .ok (.Ok _) => True := by
 cases h : actual.claim D sem v.y1 v.inactive g o.kappa with
 | fail e => simp only [NGN_Cuts.claimCut,h,bind_tc_fail]
 | div => simp only [NGN_Cuts.claimCut,h,bind_tc_div]
 | ok r =>
  cases r with
  | Ok claim => trivial
  | Err e =>
   simp only [NGN_Cuts.claimCut,h,bind_tc_ok,core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
    core.convert.FromSame]
   rfl
#print axioms complete
#print axioms query_nonok
#print axioms claim_nonok
end LIBC_PreparedErrors
