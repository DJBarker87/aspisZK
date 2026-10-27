import R1Z.PV_CB_CompressConstructors
import R1Z.PV_CB_CanonicalQuarticMore
import R1Z.PV_CB_CompressSupport
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_CB_CompressCanonicalContext
open Aeneas Aeneas.Std Result ProverRwFull
variable [ExternalTypes]
/-- Five primitive selections only. The open op223 callback is retained. -/
@[reducible] def selected (ops : ExternalFuns) : ExternalFuns :=
  {ops with
    op61 := PV_CB_CompressConstructors.fromM31
    op66 := PV_CB_CompressConstructors.fromCM31
    op67 := PV_CB_CurrentQuartic.S.add
    op69 := PV_CB_CurrentQuartic.S.mul
    op70 := PV_CB_CurrentQuartic.S.scale}

theorem retained (ops : ExternalFuns) : (selected ops).op223 = ops.op223 := rfl

theorem constructors61 (ops : ExternalFuns) :
    (ProverRwDictionaryScalar.selected ops).op61 = (selected ops).op61 := rfl

theorem constructors66 (ops : ExternalFuns) :
    (ProverRwDictionaryScalar.selected ops).op66 = (selected ops).op66 := rfl

theorem transfer (ops : ExternalFuns)
    (same61 : ops.op61 = PV_CB_CompressConstructors.fromM31)
    (same66 : ops.op66 = PV_CB_CompressConstructors.fromCM31)
    (same67 : ops.op67 = PV_CB_CurrentQuartic.S.add)
    (same69 : ops.op69 = PV_CB_CurrentQuartic.S.mul)
    (same70 : ops.op70 = PV_CB_CurrentQuartic.S.scale)
    (tag : PV_CB_CompressSupport.M) (values : Slice PV_CB_CompressSupport.M)
    (lambda : PV_CB_CompressSupport.Q) :
    @ProverRwP6CompressSource.compress _ ops tag values lambda =
    @ProverRwP6CompressSource.compress _ (selected ops) tag values lambda :=
  PV_CB_CompressSupport.congr ops (selected ops) same61 same66 same67 same69 same70 tag values lambda
#print axioms retained
#print axioms constructors61
#print axioms constructors66
#print axioms transfer
end R1Z.PV_CB_CompressCanonicalContext
