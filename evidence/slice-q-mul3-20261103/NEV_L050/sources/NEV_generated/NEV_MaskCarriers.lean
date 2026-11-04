import NBG_FieldDischarge
import FIo_QMMulValues
import ExtractedMaskQM31Exact
import SAQ_Inverse
set_option autoImplicit false
noncomputable section
namespace NEV_MaskCarriers
open Aeneas Aeneas.Std Result AspisR1
abbrev Native := FIo_Native.aspis_core.field.QM31
abbrev Mask := AspisR1SelectedMaskProbe.field.QM31
abbrev Exact := AspisV8R15.ExactTowerBase.QM31Exact

def toMask (q : Native) : Mask := ⟨⟨q.c0.a,q.c0.b⟩,⟨q.c1.a,q.c1.b⟩⟩
def fromMask (q : Mask) : Native := ⟨⟨q.c0.a,q.c0.b⟩,⟨q.c1.a,q.c1.b⟩⟩
theorem native_roundtrip (q : Native) : fromMask (toMask q)=q := by cases q;rfl
theorem mask_roundtrip (q : Mask) : toMask (fromMask q)=q := by cases q;rfl
theorem canonical (q : Native) : LPi_FieldValues.canonQ q ↔
    ExtractedMaskQM31Exact.CurrentCanonicalQM (toMask q) := Iff.rfl
theorem native_canonical (q : Native) : LPi_FieldValues.canonQ q ↔ FIo_QMValues.Canon q := Iff.rfl
theorem decoded (q : Native) : ExtractedMaskQM31Exact.decode (toMask q)=
    AspisR1CurrentWide.Proof.decodeQM (FIo_FieldBridge.qm q) := rfl

/-- Four uses of the retained canonical scalar injectivity law. No new field
arithmetic theorem is introduced for the native/mask carrier comparison. -/
theorem decode_injective (x y : Mask)
    (hx : ExtractedMaskQM31Exact.CurrentCanonicalQM x)
    (hy : ExtractedMaskQM31Exact.CurrentCanonicalQM y)
    (same : ExtractedMaskQM31Exact.decode x=ExtractedMaskQM31Exact.decode y) : x=y := by
  have a : x.c0.a=y.c0.a := SAQ_Inverse.canonical_injective _ _ hx.1.1 hy.1.1
    (congrArg (fun z : Exact=>z.re.re) same)
  have b : x.c0.b=y.c0.b := SAQ_Inverse.canonical_injective _ _ hx.1.2 hy.1.2
    (congrArg (fun z : Exact=>z.re.im) same)
  have c : x.c1.a=y.c1.a := SAQ_Inverse.canonical_injective _ _ hx.2.1 hy.2.1
    (congrArg (fun z : Exact=>z.im.re) same)
  have d : x.c1.b=y.c1.b := SAQ_Inverse.canonical_injective _ _ hx.2.2 hy.2.2
    (congrArg (fun z : Exact=>z.im.im) same)
  exact congrArg2 AspisR1SelectedMaskProbe.field.QM31.mk
    (congrArg2 AspisR1SelectedMaskProbe.field.CM31.mk a b)
    (congrArg2 AspisR1SelectedMaskProbe.field.CM31.mk c d)
#print axioms native_roundtrip
#print axioms mask_roundtrip
#print axioms canonical
#print axioms native_canonical
#print axioms decoded
#print axioms decode_injective
end NEV_MaskCarriers
end
