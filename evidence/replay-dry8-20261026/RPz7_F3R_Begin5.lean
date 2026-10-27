import RPz7_F3R_Begin9
import RPz7_F3R_ArrayAccess
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3R_Begin5
open Aeneas Aeneas.Std Result
open AspisR1PublicPreparation PreparedHashCode SourceDigestLog
attribute [local irreducible] S1SemanticCode.semanticValidated S1SemanticCode.begin9

theorem log {Hash : Type} {D : aspis_core.Digest32 Hash} {pre : r1_wire.Prefix}
    (c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 : SourceFull25.Call D pre)
    (row5 : c5.row=5#u8)
    (row6 : c6.row=6#u8)
    (row7 : c7.row=7#u8)
    (row8 : c8.row=8#u8)
    (row9 : c9.row=9#u8)
    (row10 : c10.row=10#u8)
    (row11 : c11.row=11#u8)
    (row12 : c12.row=12#u8)
    (row13 : c13.row=13#u8)
    (row14 : c14.row=14#u8)
    (same6 : c6.before=c5.after)
    (same7 : c7.before=c6.after)
    (same8 : c8.before=c7.after)
    (same9 : c9.before=c8.after)
    (same10 : c10.before=c9.after)
    (same11 : c11.before=c10.after)
    (same12 : c12.before=c11.after)
    (same13 : c13.before=c12.after)
    (same14 : c14.before=c13.after)
    (v0 v1 v2 v4 : aspis_core.field.QM31)
    (back1 : aspis_core.field.QM31 → Array aspis_core.field.QM31 10#usize) :
    observe (run (S1SemanticCode.begin5 D pre c5.before v0 v1 v2 v4 back1)).1=
      callLog c5++callLog c6++callLog c7++callLog c8++callLog c9++callLog c10++callLog c11++callLog c12++callLog c13++callLog c14 := by
  have h5 := c5.validated
  rw [row5] at h5
  have r5 := F3R_SemanticStep.returned c5 (by rw [row5];decide)
  have h6 := c6.validated
  rw [row6] at h6
  have r6 := F3R_SemanticStep.returned c6 (by rw [row6];decide)
  rw [same6] at r6
  have h7 := c7.validated
  rw [row7] at h7
  have r7 := F3R_SemanticStep.returned c7 (by rw [row7];decide)
  rw [same7] at r7
  have h8 := c8.validated
  rw [row8] at h8
  have r8 := F3R_SemanticStep.returned c8 (by rw [row8];decide)
  rw [same8] at r8
  obtain ⟨old2,back2,access2⟩ := F3R_ArrayAccess.total (back1 v4) 2#usize (by decide)
  obtain ⟨old3,back3,access3⟩ := F3R_ArrayAccess.total (back2 c5.q) 3#usize (by decide)
  obtain ⟨old4,back4,access4⟩ := F3R_ArrayAccess.total (back3 c6.q) 4#usize (by decide)
  obtain ⟨old5,back5,access5⟩ := F3R_ArrayAccess.total (back4 c7.q) 5#usize (by decide)
  unfold S1SemanticCode.begin5
  rw [h5]
  erw [F3K_CodeStep.pure_step,F3K_CodeStep.pure_step]
  erw [F3K_CodeBind.success _ _ _ r5]
  try simp only
  erw [F3K_CodeStep.pure_step]
  try simp only
  erw [F3K_CodeStep.lift_success _ _ access2]
  try simp only
  rw [h6]
  erw [F3K_CodeStep.pure_step,F3K_CodeStep.pure_step]
  erw [F3K_CodeBind.success _ _ _ r6]
  try simp only
  erw [F3K_CodeStep.pure_step]
  try simp only
  erw [F3K_CodeStep.lift_success _ _ access3]
  try simp only
  rw [h7]
  erw [F3K_CodeStep.pure_step,F3K_CodeStep.pure_step]
  erw [F3K_CodeBind.success _ _ _ r7]
  try simp only
  erw [F3K_CodeStep.pure_step]
  try simp only
  erw [F3K_CodeStep.lift_success _ _ access4]
  try simp only
  rw [h8]
  erw [F3K_CodeStep.pure_step,F3K_CodeStep.pure_step]
  erw [F3K_CodeBind.success _ _ _ r8]
  try simp only
  erw [F3K_CodeStep.pure_step]
  try simp only
  erw [F3K_CodeStep.lift_success _ _ access5]
  try simp only
  rw [← same9]
  rw [F3R_Begin9.log c9 c10 c11 c12 c13 c14 row9 row10 row11 row12 row13 row14 same10 same11 same12 same13 same14]
  rw [← same6]
  rw [← same7]
  rw [← same8]
  rw [F3J_ValidatedLog.semantic c5 (by rw [row5];decide)]
  rw [F3J_ValidatedLog.semantic c6 (by rw [row6];decide)]
  rw [F3J_ValidatedLog.semantic c7 (by rw [row7];decide)]
  rw [F3J_ValidatedLog.semantic c8 (by rw [row8];decide)]
  simp only [List.append_assoc]

#print axioms log
end AspisR1.F3R_Begin5
end
