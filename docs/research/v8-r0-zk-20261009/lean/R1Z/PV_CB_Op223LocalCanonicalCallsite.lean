import R1Z.PV_CB_ProducerLocalCallsite
import R1Z.PV_CB_ProducerReference
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_CB_Op223LocalCanonicalCallsite
open Aeneas Aeneas.Std Result ProverRwFull PV_CB_ProducerLimb PV_CB_Op223CellSupport
variable [ExternalTypes]

/-- Numerical canonical-domain source agreement is the remaining native
    obligation. The theorem transports that agreement through the actual
    complete-Result endpoint caller, using the proved16-value producer. -/
theorem endpoint (ops : ExternalFuns) (f g : Compressor)
    (trace : Trace) (tuple : PV_CB_ProducerTuple.Tuple)
    (vt : PV_CB_CanonicalArrays.Valid (PV_CB_ProducerLocalLimb.Reads trace) tuple.limbs)
    (vo : PV_CB_CanonicalArrays.Valid OffsetValid tuple.limbs)
    (tag : U32) (lambda : Q) (vtag : PV_CB_CanonicalM31.Valid tag)
    (vlambda : PV_CB_CanonicalTower.Valid lambda)
    (source16 : ∀ tag (data : Array U32 16#usize) lambda,
      PV_CB_CanonicalM31.Valid tag →
      PV_CB_CanonicalArrays.Valid PV_CB_CanonicalM31.Valid data →
      PV_CB_CanonicalTower.Valid lambda →
      f tag (Array.to_slice data) lambda = g tag (Array.to_slice data) lambda)
    (side : Usize) (values : PV_CB_Op223Callsite.Values) (arity : PV_CB_Op223Callsite.Arity) :
    @host_semantic.copy_endpoint_values _ {(PV_CurrentScaleInstall.selected ops) with op223 := f}
      trace tuple tag lambda side values arity =
    @host_semantic.copy_endpoint_values _ {(PV_CurrentScaleInstall.selected ops) with op223 := g}
      trace tuple tag lambda side values arity :=
  PV_CB_ProducerLocalCallsite.endpoint ops f g trace tuple vt vo tag lambda
    (fun data vd => source16 tag data lambda vtag vd vlambda) side values arity
#print axioms endpoint
end R1Z.PV_CB_Op223LocalCanonicalCallsite
