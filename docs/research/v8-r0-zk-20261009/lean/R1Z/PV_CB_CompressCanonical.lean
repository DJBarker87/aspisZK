import R1Z.PV_CB_CompressCanonicalFinite
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_CB_CompressCanonical
open Aeneas Aeneas.Std Result ProverRwFull
variable [ExternalTypes]
abbrev Q := PV_CB_CanonicalTower.Q

theorem reference (ops : ExternalFuns) (tag : U32) (values : Slice U32) (lambda : Q)
    (vt : PV_CB_CanonicalM31.Valid tag) (vv : PV_CB_CompressCanonicalRead.Valid values)
    (vl : PV_CB_CanonicalTower.Valid lambda) :
    ∃ result, @ProverRwP6CompressSource.compress _ (PV_CB_CompressCanonicalContext.selected ops)
      tag values lambda = ok result ∧ PV_CB_CanonicalTower.Valid result := by
  obtain ⟨c,hc,vc⟩ := PV_CB_CompressConstructors.m31_valid tag vt
  obtain ⟨q,hq,vq⟩ := PV_CB_CompressConstructors.cm31_valid c vc
  obtain ⟨result,hresult,vresult⟩ := PV_CB_CompressCanonicalFinite.finite ops values lambda
    (Slice.len values).val q lambda 0#usize (by change 0+_= _;omega) vv vl vq vl
  refine ⟨result,?_,vresult⟩
  rw [@ProverRwP6CompressControl.compress_finite _ (PV_CB_CompressCanonicalContext.selected ops) tag values lambda]
  change (do
    let c ← PV_CB_CompressConstructors.fromM31 tag
    let q ← PV_CB_CompressConstructors.fromCM31 c
    @ProverRwP6CompressControl.finite _ (PV_CB_CompressCanonicalContext.selected ops)
      values lambda (Slice.len values).val q lambda 0#usize) = ok result
  simp only [hc,hq,hresult,bind_tc_ok]

/-- Local primitive source equations transport the invariant. This is not an
    op223 source equation, and is not installed into the privacy endpoint. -/
theorem of_callbacks (ops : ExternalFuns)
    (same61 : ops.op61 = PV_CB_CompressConstructors.fromM31)
    (same66 : ops.op66 = PV_CB_CompressConstructors.fromCM31)
    (same67 : ops.op67 = PV_CB_CurrentQuartic.S.add)
    (same69 : ops.op69 = PV_CB_CurrentQuartic.S.mul)
    (same70 : ops.op70 = PV_CB_CurrentQuartic.S.scale)
    (tag : U32) (values : Slice U32) (lambda : Q)
    (vt : PV_CB_CanonicalM31.Valid tag) (vv : PV_CB_CompressCanonicalRead.Valid values)
    (vl : PV_CB_CanonicalTower.Valid lambda) :
    ∃ result, @ProverRwP6CompressSource.compress _ ops tag values lambda = ok result ∧
      PV_CB_CanonicalTower.Valid result := by
  obtain ⟨result,hresult,vresult⟩ := reference ops tag values lambda vt vv vl
  exact ⟨result,(PV_CB_CompressCanonicalContext.transfer ops same61 same66 same67 same69 same70 tag values lambda).trans hresult,vresult⟩
#print axioms reference
#print axioms of_callbacks
end R1Z.PV_CB_CompressCanonical
