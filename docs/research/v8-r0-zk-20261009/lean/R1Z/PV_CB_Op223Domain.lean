import R1Z.ProverRwP6CompressControl
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_CB_Op223Domain
open Aeneas Aeneas.Std Result ProverRwFull
variable [ExternalTypes] [ExternalFuns]
abbrev M := aspis_core.field.M31
abbrev Q := aspis_core.field.QM31
/-- The shape returned by the actual cost-probe copy_tuple_values caller. -/
def Canonical (values : Slice M) : Prop := values.length = 16

theorem array_domain (values : Array M 16#usize) :
    Canonical (Array.to_slice values) := by
  simp only [Canonical,Array.to_slice,Slice.length]
  exact values.property

theorem len_val (values : Slice M) (canonical : Canonical values) :
    (Slice.len values).val = 16 := by
  change values.val.length = 16
  exact canonical

theorem source_finite16 (tag : M) (values : Slice M) (lambda : Q)
    (canonical : Canonical values) :
    ProverRwP6CompressSource.compress tag values lambda = (do
      let c ← aspis_core.field.CM31.from_m31 tag
      let out ← aspis_core.field.QM31.from_cm31 c
      ProverRwP6CompressControl.finite values lambda 16 out lambda 0#usize) := by
  rw [ProverRwP6CompressControl.compress_finite,len_val values canonical]
#print axioms array_domain
#print axioms len_val
#print axioms source_finite16
end R1Z.PV_CB_Op223Domain
