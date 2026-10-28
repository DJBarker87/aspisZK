import R1Z.PV_RunJoin_InterpolationComplete38
import R1Z.PV_RunJoin_PolyComplete38
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_InterpolationPipeline38
open Aeneas Aeneas.Std Result ProverRwFull
open PV_RunJoin_FieldData34 PV_RunJoin_MergeArray35 PV_RunJoin_AccPolynomial38
variable [ExternalTypes]

/-- Concrete current-emission interpolation and serialization composition.
Every serialized coefficient is the corresponding independent Lagrange
coefficient. Caller sample provenance and native effects remain separate. -/
theorem complete (ops : ExternalFuns) (values : Nat → Q) :
    ∃ (out : Nat → Q) (bytes : alloc.vec.Vec U8),
      @host_sumcheck.interpolate _ (ProverRwP6BodyCandidate.selected ops) (array values)=.ok (array out) ∧
      @host_sumcheck.encode_polynomial _ (ProverRwP6BodyCandidate.selected ops) (array out)=.ok bytes ∧
      bytes.val=PV_RunJoin_PolyLoop38.payload out 0 28 ∧ bytes.val.length=896 ∧
      (∀ k, k<28 → canonical (out k)) ∧
      ∀ k : Fin 28, value (out k.val)=
        (Lagrange.interpolate Finset.univ
          (fun j : Fin 28 => (j.val : AspisR1.ExtractedCurrentQM31Exact.QM31Exact))
          (fun j => value (values j.val))).coeff k.val := by
  obtain ⟨out,hout,hcan,hpoly⟩ := PV_RunJoin_InterpolationComplete38.interpolate ops values
  obtain ⟨bytes,hbytes,hval,hlen⟩ := PV_RunJoin_PolyComplete38.encode ops out
  refine ⟨out,bytes,hout,hbytes,hval,hlen,hcan,?_⟩
  intro k
  have eq := congrArg (fun p : Polynomial AspisR1.ExtractedCurrentQM31Exact.QM31Exact => p.coeff k.val) hpoly
  simpa only [value,poly,ProverCommitInterpolationRow48.qpoly,ProverCommitInterpolationPoly48.coeff,
    if_pos k.isLt] using eq

#print axioms complete
end R1Z.PV_RunJoin_InterpolationPipeline38
