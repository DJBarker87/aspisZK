import NEV_MaskQM
import NBO_FieldSemantics
set_option autoImplicit false
noncomputable section
namespace NEV_StageFields
open Aeneas Aeneas.Std Result AspisR1
abbrev Q := NBF_RowInstall.Q
abbrev E := NBF_RowInstall.E
abbrev NQ := NEV_MaskCarriers.Native
abbrev NE := FIo_Native.aspis_core.field.wide_exact.WideExact

def nq (q : Q) : NQ := ⟨⟨q.c0.a,q.c0.b⟩,⟨q.c1.a,q.c1.b⟩⟩
def sq (q : NQ) : Q := ⟨⟨q.c0.a,q.c0.b⟩,⟨q.c1.a,q.c1.b⟩⟩
def ne (e : E) : NE := ⟨nq e.c0,nq e.c1⟩
def se (e : NE) : E := ⟨sq e.c0,sq e.c1⟩
theorem native_q_roundtrip (q : NQ) : nq (sq q)=q := by cases q;rfl
theorem stage_q_roundtrip (q : Q) : sq (nq q)=q := by cases q;rfl
theorem native_e_roundtrip (e : NE) : ne (se e)=e := by cases e;rfl
theorem stage_e_roundtrip (e : E) : se (ne e)=e := by cases e;rfl

theorem canonical_q (q : Q) : NBF_PowerStep.Canonical q ↔ LPi_FieldValues.canonQ (nq q) :=
  (NBO_FieldPorts.canonicalQ q).trans (NEV_MaskCarriers.canonical (nq q)).symm
theorem canonical_e (e : E) : NBO_TailDomain.WideCanonical e ↔ LPi_FieldValues.canonE (ne e) :=
  and_congr (canonical_q e.c0) (canonical_q e.c1)

/-- Actual emitted QM31 call agrees with the already adopted NBO scalar
callback. Both totality/value laws are imported, never arithmetic in Kani. -/
theorem power (x y : Q) (hx : NBF_PowerStep.Canonical x) (hy : NBF_PowerStep.Canonical y) :
    (do let out ← FIo_Native.aspis_core.field.QM31.mul (nq x) (nq y);ok (sq out)) =
      NBO_FieldSemantics.power x y := by
  have same := NEV_MaskQM.multiply (nq x) (nq y) ((canonical_q x).mp hx) ((canonical_q y).mp hy)
  have lifted := congrArg (fun result : Result NEV_MaskCarriers.Mask =>
    do let out ← result;ok (NBO_FieldPorts.fromQ out)) same
  simpa only [NBO_FieldSemantics.power,NBO_FieldPorts.toQ,NBO_FieldPorts.fromQ,
    NEV_MaskCarriers.toMask,nq,sq,bind_assoc_eq,bind_tc_ok] using lifted
#print axioms native_q_roundtrip
#print axioms stage_q_roundtrip
#print axioms native_e_roundtrip
#print axioms stage_e_roundtrip
#print axioms canonical_q
#print axioms canonical_e
#print axioms power
end NEV_StageFields
end
