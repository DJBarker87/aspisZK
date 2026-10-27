import R1Z.PV_CB_CompressCanonical
import R1Z.PV_CB_CanonicalArrays
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_CB_CompressCanonicalArray16
open Aeneas Aeneas.Std Result ProverRwFull
variable [ExternalTypes]

theorem slice_valid {N : Usize} (values : Array U32 N)
    (valid : PV_CB_CanonicalArrays.Valid PV_CB_CanonicalM31.Valid values) :
    PV_CB_CompressCanonicalRead.Valid (Array.to_slice values) := valid

/-- Exact16-element source-reference domain of copy_endpoint_values. Native
    shipped/reference equality is not assumed or concluded here. -/
theorem reference (ops : ExternalFuns) (tag : U32) (values : Array U32 16#usize)
    (lambda : PV_CB_CanonicalTower.Q) (vt : PV_CB_CanonicalM31.Valid tag)
    (vv : PV_CB_CanonicalArrays.Valid PV_CB_CanonicalM31.Valid values)
    (vl : PV_CB_CanonicalTower.Valid lambda) :
    ∃ result, @ProverRwP6CompressSource.compress _ (PV_CB_CompressCanonicalContext.selected ops)
      tag (Array.to_slice values) lambda = ok result ∧ PV_CB_CanonicalTower.Valid result :=
  PV_CB_CompressCanonical.reference ops tag _ lambda vt (slice_valid values vv) vl
#print axioms slice_valid
#print axioms reference
end R1Z.PV_CB_CompressCanonicalArray16
