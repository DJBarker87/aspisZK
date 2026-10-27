import R1Z.PV_CB_Op223TagCanonical
import R1Z.PV_CB_CanonicalSampler
import R1Z.PV_CB_CompressCanonicalArray16
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_CB_Op223CanonicalDomain
open Aeneas Aeneas.Std Result ProverRwFull
variable [ExternalTypes]

/-- The extracted tag expression and retained block sampler supply two
    numerical invariants, without desired-output hypotheses. The array
    invariant and the native callback association remain caller obligations. -/
theorem reference (ops : ExternalFuns) (id : U16) (block : Array U8 32#usize)
    (values : Array U32 16#usize)
    (vv : PV_CB_CanonicalArrays.Valid PV_CB_CanonicalM31.Valid values) :
    ∃ result, (do
      let tag ← PV_CB_ShippedOp223Tag.copy_tag id
      let lambda ← ProverRwFullSampler.selected block
      @ProverRwP6CompressSource.compress _ (PV_CB_CompressCanonicalContext.selected ops)
        tag (Array.to_slice values) lambda) = ok result ∧ PV_CB_CanonicalTower.Valid result := by
  obtain ⟨lambda,hlambda,vlambda⟩ := PV_CB_CanonicalSampler.selected block
  obtain ⟨result,hresult,vresult⟩ := PV_CB_CompressCanonicalArray16.reference ops
    (PV_CB_Op223TagCanonical.tag id) values lambda (PV_CB_Op223TagCanonical.canonical id) vv vlambda
  refine ⟨result,?_,vresult⟩
  simp only [PV_CB_Op223TagCanonical.expression,hlambda,hresult,bind_tc_ok]
#print axioms reference
end R1Z.PV_CB_Op223CanonicalDomain
