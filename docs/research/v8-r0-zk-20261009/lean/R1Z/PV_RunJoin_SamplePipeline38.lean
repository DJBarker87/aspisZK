import R1Z.PV_RunJoin_InterpolationPipeline38
import R1Z.PV_RunJoin_MergeInstall35
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_SamplePipeline38
open Aeneas Aeneas.Std Result ProverRwFull
open PV_RunJoin_FieldData34 PV_RunJoin_MergeArray35
variable [ExternalTypes]

/-- Concrete source pipeline after the ordered worker evaluations have been
supplied. The merged samples, interpolated coefficients and exact payload all
come from their complete source laws. Associating these supplied cells with
the actual oracle/workers remains a separate obligation. -/
theorem complete (ops : ExternalFuns) (r : Usize) (hr : r.val<10)
    (es : Nat → Q) (he : ∀ j, j<(PV_RunJoin_SampleDomain34.count r).val → canonical (es j)) :
    ∃ (merged coefficients : Nat → Q) (bytes : alloc.vec.Vec U8),
      @host_sumcheck.merge_evaluations _ (ProverRwP6BodyCandidate.selected ops)
        (Array.to_slice (ProverCommitArray49.array (PV_RunJoin_SampleDomain34.count r)
          (fun j => core.result.Result.Ok (es j)))) (PV_RunJoin_SampleDomain34.assignments r) =
          .ok (.Ok (array merged)) ∧
      @host_sumcheck.interpolate _ (ProverRwP6BodyCandidate.selected ops) (array merged)=.ok (array coefficients) ∧
      @host_sumcheck.encode_polynomial _ (ProverRwP6BodyCandidate.selected ops) (array coefficients)=.ok bytes ∧
      bytes.val=PV_RunJoin_PolyLoop38.payload coefficients 0 28 ∧ bytes.val.length=896 ∧
      (∀ k, k<28 → canonical (coefficients k)) ∧
      ∀ k : Fin 28, value (coefficients k.val)=
        (Lagrange.interpolate Finset.univ
          (fun j : Fin 28 => (j.val : AspisR1.ExtractedCurrentQM31Exact.QM31Exact))
          (fun k : Fin 28 => ∑ j ∈ Finset.range (PV_RunJoin_SampleDomain34.count r).val,
            if j/(PV_RunJoin_SampleDomain34.assignments r).val=k.val then value (es j) else 0)).coeff k.val := by
  obtain ⟨merged,hmerged,hcm,hvm⟩ := PV_RunJoin_MergeInstall35.installed ops r hr es he
  obtain ⟨coefficients,bytes,hinterp,hbytes,hpayload,hlen,hcan,hcoeff⟩ :=
    PV_RunJoin_InterpolationPipeline38.complete ops merged
  refine ⟨merged,coefficients,bytes,hmerged,hinterp,hbytes,hpayload,hlen,hcan,?_⟩
  intro k
  simpa only [hvm] using hcoeff k

#print axioms complete
end R1Z.PV_RunJoin_SamplePipeline38
