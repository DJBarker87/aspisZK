import R1Z.PV_CB_CompressCanonical
import R1Z.PV_CB_CompressSelectedEntries
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_CB_CompressSelectedCanonical
open Aeneas Aeneas.Std Result ProverRwFull
variable [ExternalTypes]

theorem context (ops : ExternalFuns) (tag : U32) (values : Slice U32)
    (lambda : PV_CB_CanonicalTower.Q) :
    @ProverRwP6CompressSource.compress _ (PV_CurrentScaleInstall.selected ops) tag values lambda =
    @ProverRwP6CompressSource.compress _ (PV_CB_CompressCanonicalContext.selected
      (PV_CurrentScaleInstall.selected ops)) tag values lambda :=
  PV_CB_CompressCanonicalContext.transfer (PV_CurrentScaleInstall.selected ops)
    (PV_CB_CompressSelectedEntries.entry61 ops) (PV_CB_CompressSelectedEntries.entry66 ops)
    (PV_CB_CompressSelectedEntries.entry67 ops) (PV_CB_CompressSelectedEntries.entry69 ops)
    (PV_CB_CompressSelectedEntries.entry70 ops) tag values lambda

theorem reference (ops : ExternalFuns) (tag : U32) (values : Slice U32)
    (lambda : PV_CB_CanonicalTower.Q) (vt : PV_CB_CanonicalM31.Valid tag)
    (vv : PV_CB_CompressCanonicalRead.Valid values) (vl : PV_CB_CanonicalTower.Valid lambda) :
    ∃ result, @ProverRwP6CompressSource.compress _ (PV_CurrentScaleInstall.selected ops)
      tag values lambda = ok result ∧ PV_CB_CanonicalTower.Valid result := by
  obtain ⟨result,hr,vr⟩ := PV_CB_CompressCanonical.reference
    (PV_CurrentScaleInstall.selected ops) tag values lambda vt vv vl
  exact ⟨result,(context ops tag values lambda).trans hr,vr⟩
#print axioms context
#print axioms reference
end R1Z.PV_CB_CompressSelectedCanonical
