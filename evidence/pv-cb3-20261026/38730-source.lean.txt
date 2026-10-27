import R1Z.PV_CB3_StagedNativeLink
import R1Z.PV_CB3_StagedValue
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_CB3_NormalizeIdentity
open Aeneas Aeneas.Std Result ProverRwFull

def Canonical (x : aspis_core.field.QM31) : Prop :=
  (x.c0.a.val < 2147483647 ∧ x.c0.b.val < 2147483647) ∧
  (x.c1.a.val < 2147483647 ∧ x.c1.b.val < 2147483647)

theorem word (x : U32) (h : x.val < 2147483647) :
    ProverCommitNativeOps47.normalizeWord x = x := by
  apply UScalar.eq_of_val_eq
  rw [ProverCommitNativeOps47.normalize_val,Nat.mod_eq_of_lt h]

theorem normalized (x : aspis_core.field.QM31) (h : Canonical x) :
    ProverRwSuccessNativeNormalize.normalized x = x := by
  rcases x with ⟨⟨a,b⟩,⟨c,d⟩⟩
  simp only [Canonical] at h
  simp only [ProverRwSuccessNativeNormalize.normalized,
    word a h.1.1,word b h.1.2,word c h.2.1,word d h.2.2]

theorem source (x : aspis_core.field.QM31) (h : Canonical x) :
    PV_CB3_StagedFields.aspis_core.field.wide_exact.canonical_qm31 x = ok x := by
  calc
    _ = ProverRwSuccessNativePorts.aspis_core.field.wide_exact.canonical_qm31 x :=
      PV_CB3_StagedNativeLink.canonical x
    _ = ok (ProverRwSuccessNativeNormalize.normalized x) :=
      ProverRwSuccessNativeNormalize.native x
    _ = ok x := congrArg ok (normalized x h)
#print axioms word
#print axioms normalized
#print axioms source
end R1Z.PV_CB3_NormalizeIdentity
