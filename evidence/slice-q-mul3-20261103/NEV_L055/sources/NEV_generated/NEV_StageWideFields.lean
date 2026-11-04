import NEV_StageFields
set_option autoImplicit false
noncomputable section
namespace NEV_StageWideFields
open Aeneas Aeneas.Std Result AspisR1 NEV_StageFields

theorem add (x y : E) (hx : NBO_TailDomain.WideCanonical x) (hy : NBO_TailDomain.WideCanonical y) :
    (do let out ← FIo_Native.aspis_core.field.wide_exact.WideExact.add (ne x) (ne y);ok (se out)) =
      NBO_FieldSemantics.add x y := by
  have cx := (canonical_e x).mp hx
  have cy := (canonical_e y).mp hy
  obtain ⟨a,ha,ca,_⟩ := LPi_TowerValues.qm_add (nq x.c0) (nq y.c0) cx.1 cy.1
  obtain ⟨b,hb,cb,_⟩ := LPi_TowerValues.qm_add (nq x.c1) (nq y.c1) cx.2 cy.2
  have ma : AspisR1SelectedMaskProbe.field.QM31.add (NBO_FieldPorts.toQ x.c0)
      (NBO_FieldPorts.toQ y.c0)=ok (NEV_MaskCarriers.toMask a) := by
    have same := NEV_MaskQM.add (nq x.c0) (nq y.c0) cx.1 cy.1
    exact same.symm.trans (by simp only [ha,bind_tc_ok])
  have mb : AspisR1SelectedMaskProbe.field.QM31.add (NBO_FieldPorts.toQ x.c1)
      (NBO_FieldPorts.toQ y.c1)=ok (NEV_MaskCarriers.toMask b) := by
    have same := NEV_MaskQM.add (nq x.c1) (nq y.c1) cx.2 cy.2
    exact same.symm.trans (by simp only [hb,bind_tc_ok])
  simp only [FIo_Native.aspis_core.field.wide_exact.WideExact.add,ne,ha,hb,
    NBO_FieldSemantics.add,ma,mb,bind_tc_ok,se,sq,NBO_FieldPorts.fromE,
    NBO_FieldPorts.fromQ,NEV_MaskCarriers.toMask]

/-- The actual normalization call and both actual component products return
exactly the adopted callback's value, on caller-established canonical inputs. -/
theorem product (x : E) (q : Q) (hx : NBO_TailDomain.WideCanonical x)
    (hq : NBF_PowerStep.Canonical q) :
    (do let out ← FIo_Native.aspis_core.field.wide_exact.WideExact.mul_qm31 (ne x) (nq q);ok (se out)) =
      NBO_FieldSemantics.product x q := by
  have cx := (canonical_e x).mp hx
  have cq := (canonical_q q).mp hq
  have normalized := NEV_MaskQM.normalization (nq q) cq
  obtain ⟨a,ha,ca,_⟩ := LPi_TowerValues.qm_mul (nq x.c0) (nq q) cx.1 cq
  obtain ⟨b,hb,cb,_⟩ := LPi_TowerValues.qm_mul (nq x.c1) (nq q) cx.2 cq
  have ma : AspisR1SelectedMaskProbe.field.QM31.mul (NBO_FieldPorts.toQ x.c0)
      (NBO_FieldPorts.toQ q)=ok (NEV_MaskCarriers.toMask a) := by
    have same := NEV_MaskQM.multiply (nq x.c0) (nq q) cx.1 cq
    exact same.symm.trans (by simp only [ha,bind_tc_ok])
  have mb : AspisR1SelectedMaskProbe.field.QM31.mul (NBO_FieldPorts.toQ x.c1)
      (NBO_FieldPorts.toQ q)=ok (NEV_MaskCarriers.toMask b) := by
    have same := NEV_MaskQM.multiply (nq x.c1) (nq q) cx.2 cq
    exact same.symm.trans (by simp only [hb,bind_tc_ok])
  simp only [FIo_Native.aspis_core.field.wide_exact.WideExact.mul_qm31,ne,normalized,ha,hb,
    NBO_FieldSemantics.product,ma,mb,bind_tc_ok,se,sq,NBO_FieldPorts.fromE,
    NBO_FieldPorts.fromQ,NEV_MaskCarriers.toMask]
#print axioms add
#print axioms product
end NEV_StageWideFields
end
