import R1Z.ProverCommitSemanticModel55
import R1Z.ProverCommitBoundaryPolynomial49
import R1Z.ProverCommitEval50
import R1Z.ProverCommitInterpolationRow48
/-! Actual canonical source boundary comparisons and round-to-round running
values. Polynomial provenance is consumed at this caller cut. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverCommitSemanticGuards55
open Aeneas Aeneas.Std Result AspisR1ProducerRelease47
open ProverCommitPrimitive47 ProverCommitSubfieldOps47
open AspisR1.ExtractedCurrentQM31Exact (decode QM31Exact)
open ProverCommitInterpolationRow48
open R0P R0P.SemSource R0P.Sumcheck R0Z.HonestView R0Z.PayloadSplit R0Z.RefPayload
variable {F : Subfield QM31Exact}
attribute [local instance] Classical.propDecidable

def boundaryMatch (p : Nat → Old.Q) (running : Old.Q) : Result Bool := do
  let value ← ProverCommitBoundaryPolynomial49.run p
  ok (decide (value=ProverCommitNativeQ48.source running))

theorem qpoly_boundary (p : Nat → Old.Q) : ProverCommitBoundaryPolynomial49.poly p=qpoly p := rfl

theorem no_rejection (p : Nat → Old.Q) (running : Old.Q) (hr : Canonical running)
    (hd : decode running=(qpoly p).eval 0+(qpoly p).eval 1) : boundaryMatch p running=ok true := by
  have h := ProverCommitBoundaryPolynomial49.exact_result p
  have hv : decode (ProverCommitBoundaryValue49.output p)=decode running := by
    rw [h.2.2,qpoly_boundary,hd]
  have heq : ProverCommitBoundaryValue49.output p=running :=
    (AspisR1.ExtractedCurrentQM31Equality.decode_eq_iff _ _ h.2.1 hr).mp hv
  rw [boundaryMatch,h.1,heq]
  simp only [bind_tc_ok,decide_true]

theorem initial (pi : Fin 1024 ≃ Fin 1024) (pub : Public QM31Exact) (B : PackBasis F)
    (ch : Challenges QM31Exact) (t : Trace QM31Exact) (p : Nat → Old.Q)
    (hp : qpoly p=rounds ch 0 (ProverCommitSemanticModel55.oracle pi pub B ch t))
    (running : Old.Q) (hr : Canonical running)
    (hrun : decode running=bsumB 10 (fun b => maskLinear pi B (ofBool b) t)+S0 pub B ch) :
    boundaryMatch p running=ok true := by
  apply no_rejection p running hr
  rw [hp,ProverCommitSemanticModel55.initial_guard,hrun]

theorem chain (pi : Fin 1024 ≃ Fin 1024) (pub : Public QM31Exact) (B : PackBasis F)
    (ch : Challenges QM31Exact) (t : Trace QM31Exact) (r : Fin 9)
    (previous current : Nat → Old.Q) (hc : ∀ i, i<28 → Canonical (previous i))
    (hprevious : qpoly previous=rounds ch r.castSucc (ProverCommitSemanticModel55.oracle pi pub B ch t))
    (hcurrent : qpoly current=rounds ch r.succ (ProverCommitSemanticModel55.oracle pi pub B ch t))
    (a : Old.Q) (ha : Canonical a) (haval : decode a=alpha ch r.castSucc) :
    ∃ running : Old.Q,
      eval50.eval (ProverCommitEvalBlock50.source previous) (ProverCommitNativeQ48.source a)=
        ok (ProverCommitNativeQ48.source running) ∧
      Canonical running ∧ boundaryMatch current running=ok true := by
  obtain ⟨running,hrun,hcrun,hdrun⟩ := ProverCommitEval50.exact_result previous a hc ha
  refine ⟨running,hrun,hcrun,no_rejection current running hcrun ?_⟩
  change decode running=(qpoly previous).eval (decode a) at hdrun
  rw [hdrun,hprevious,hcurrent,haval,ProverCommitSemanticModel55.chain_guard]

#print axioms qpoly_boundary
#print axioms no_rejection
#print axioms initial
#print axioms chain
end R1Z.ProverCommitSemanticGuards55
