import Lean
import NFN_PhaseTransport
import NFS_NBG_FieldDischarge
import ExtractedMaskQM31Mul

set_option autoImplicit false
noncomputable section
namespace NFS_NEV_MaskCarriers
open Aeneas Aeneas.Std Result AspisR1
abbrev Native := FIo_Native.aspis_core.field.QM31
abbrev Mask := AspisR1SelectedMaskProbe.field.QM31
abbrev Words := (Nat × Nat) × (Nat × Nat)

def toMask (q : Native) : Mask := ⟨⟨q.c0.a,q.c0.b⟩,⟨q.c1.a,q.c1.b⟩⟩
def fromMask (q : Mask) : Native := ⟨⟨q.c0.a,q.c0.b⟩,⟨q.c1.a,q.c1.b⟩⟩
theorem native_roundtrip (q : Native) : fromMask (toMask q)=q := by cases q;rfl
theorem mask_roundtrip (q : Mask) : toMask (fromMask q)=q := by cases q;rfl
theorem canonical (q : Native) : NFN_LPi_FieldValues.canonQ q ↔
    ExtractedMaskTowerAdd.CanonicalQM (toMask q) := Iff.rfl
theorem words (q : Native) : ExtractedMaskQM31Mul.wordsQM (toMask q)=NFN_LPi_FieldValues.qw q := rfl
/-- The two imported natural-word product definitions are literally the same
Karatsuba formula. No multiplication theorem is reproved. -/
theorem product_words (x y : Words) : NFN_LPi_FieldValues.mulQ x y=ExtractedMaskQM31Mul.qmMulWords x y := rfl

theorem words_injective (x y : Mask)
    (same : ExtractedMaskQM31Mul.wordsQM x=ExtractedMaskQM31Mul.wordsQM y) : x=y := by
  have a : x.c0.a=y.c0.a := UScalar.eq_of_val_eq (congrArg (fun z : Words=>z.1.1) same)
  have b : x.c0.b=y.c0.b := UScalar.eq_of_val_eq (congrArg (fun z : Words=>z.1.2) same)
  have c : x.c1.a=y.c1.a := UScalar.eq_of_val_eq (congrArg (fun z : Words=>z.2.1) same)
  have d : x.c1.b=y.c1.b := UScalar.eq_of_val_eq (congrArg (fun z : Words=>z.2.2) same)
  exact congrArg₂ AspisR1SelectedMaskProbe.field.QM31.mk
    (congrArg₂ AspisR1SelectedMaskProbe.field.CM31.mk a b)
    (congrArg₂ AspisR1SelectedMaskProbe.field.CM31.mk c d)
theorem native_injective (x y : Native) (same : NFN_LPi_FieldValues.qw x=NFN_LPi_FieldValues.qw y) : x=y := by
  have transported : toMask x=toMask y := words_injective _ _
    (by simpa only [words] using same)
  have result := congrArg fromMask transported
  simpa only [native_roundtrip] using result
#print axioms native_roundtrip
#print axioms mask_roundtrip
#print axioms canonical
#print axioms words
#print axioms product_words
#print axioms words_injective
#print axioms native_injective
end NFS_NEV_MaskCarriers
end

run_cmd do
 let env ← Lean.getEnv
 env.constants.toList.forM fun (n, ci) => do
  if ci.isTheorem && (env.getModuleIdxFor? n).isNone then
   Lean.Elab.Command.elabCommand (← `(command| #print axioms $(Lean.mkIdent n)))
