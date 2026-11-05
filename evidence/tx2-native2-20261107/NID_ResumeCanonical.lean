import NHV_COMBINED_IMPORT
import CheckpointBytes4SuccessfulFields
set_option autoImplicit false
noncomputable section
namespace NID_ResumeCanonical
open Aeneas Aeneas.Std Result AspisR1 AspisR1Stage2
open CheckpointBytes4ReaderFields CheckpointBytes4Layout

def KCanonical (q : aspis_core.field.QM31) : Prop :=
 q.c0.a.val<2147483647 ∧ q.c0.b.val<2147483647 ∧
 q.c1.a.val<2147483647 ∧ q.c1.b.val<2147483647

def ECanonical (x : aspis_core.field.wide_exact.WideExact) : Prop :=
 KCanonical x.c0 ∧ KCanonical x.c1

-- Same codec-value argument as NCI_ResumeDomains.sourceK_canonical; no native credit.
theorem sourceK_canonical (x : OraclePortCheckpointAbiC5.K) : KCanonical (sourceK x) := by
 simp only [KCanonical,sourceK,CheckpointBytes3Namespaces.fromK,CheckpointBytes3KDecode.rawK,
  CheckpointBytes3KDecode.rawLimbs,CheckpointBytes3ScalarShape.kWords,M31ParserRefinement.valueToU32_val]
 exact ⟨(RetainedExactLimbCodec.qm31ExactLimbEquiv.symm x 0).isLt,
  (RetainedExactLimbCodec.qm31ExactLimbEquiv.symm x 1).isLt,
  (RetainedExactLimbCodec.qm31ExactLimbEquiv.symm x 2).isLt,
  (RetainedExactLimbCodec.qm31ExactLimbEquiv.symm x 3).isLt⟩

theorem sourceE_canonical (x : OraclePortCheckpointAbiC5.E) : ECanonical (sourceE x) := by
 change KCanonical (sourceK x.re) ∧ KCanonical (sourceK x.im)
 exact ⟨sourceK_canonical x.re,sourceK_canonical x.im⟩

theorem k_at (ck : Slice U8) (offset : Nat) (q : aspis_core.field.QM31)
 (read : KAt ck offset q) : KCanonical q := by
 obtain ⟨x,_,rfl⟩ := read
 exact sourceK_canonical x

theorem e_at (ck : Slice U8) (offset : Nat) (q : aspis_core.field.wide_exact.WideExact)
 (read : EAt ck offset q) : ECanonical q := by
 obtain ⟨x,_,rfl⟩ := read
 exact sourceE_canonical x

#print axioms sourceK_canonical
#print axioms sourceE_canonical
#print axioms k_at
#print axioms e_at
end NID_ResumeCanonical
