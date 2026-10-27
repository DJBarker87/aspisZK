import RPz7_F3R_Begin13
import RPz7_F3R_ArrayAccess
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3R_Begin9
open Aeneas Aeneas.Std Result
open AspisR1PublicPreparation PreparedHashCode SourceDigestLog
attribute [local irreducible] S1SemanticCode.semanticValidated S1SemanticCode.begin13

theorem log {Hash : Type} {D : aspis_core.Digest32 Hash} {pre : r1_wire.Prefix}
    (c9 c10 c11 c12 c13 c14 : SourceFull25.Call D pre)
    (row9 : c9.row=9#u8)
    (row10 : c10.row=10#u8)
    (row11 : c11.row=11#u8)
    (row12 : c12.row=12#u8)
    (row13 : c13.row=13#u8)
    (row14 : c14.row=14#u8)
    (same10 : c10.before=c9.after)
    (same11 : c11.before=c10.after)
    (same12 : c12.before=c11.after)
    (same13 : c13.before=c12.after)
    (same14 : c14.before=c13.after)
    (v0 v1 v2 v8 : aspis_core.field.QM31)
    (back5 : aspis_core.field.QM31 → Array aspis_core.field.QM31 10#usize) :
    observe (run (S1SemanticCode.begin9 D pre c9.before v0 v1 v2 v8 back5)).1=
      callLog c9++callLog c10++callLog c11++callLog c12++callLog c13++callLog c14 := by
  have h9 := c9.validated
  rw [row9] at h9
  have r9 := F3R_SemanticStep.returned c9 (by rw [row9];decide)
  have h10 := c10.validated
  rw [row10] at h10
  have r10 := F3R_SemanticStep.returned c10 (by rw [row10];decide)
  rw [same10] at r10
  have h11 := c11.validated
  rw [row11] at h11
  have r11 := F3R_SemanticStep.returned c11 (by rw [row11];decide)
  rw [same11] at r11
  have h12 := c12.validated
  rw [row12] at h12
  have r12 := F3R_SemanticStep.returned c12 (by rw [row12];decide)
  rw [same12] at r12
  obtain ⟨old6,back6,access6⟩ := F3R_ArrayAccess.total (back5 v8) 6#usize (by decide)
  obtain ⟨old7,back7,access7⟩ := F3R_ArrayAccess.total (back6 c9.q) 7#usize (by decide)
  obtain ⟨old8,back8,access8⟩ := F3R_ArrayAccess.total (back7 c10.q) 8#usize (by decide)
  obtain ⟨old9,back9,access9⟩ := F3R_ArrayAccess.total (back8 c11.q) 9#usize (by decide)
  unfold S1SemanticCode.begin9
  rw [h9]
  erw [F3K_CodeStep.pure_step,F3K_CodeStep.pure_step]
  erw [F3K_CodeBind.success _ _ _ r9]
  try simp only
  erw [F3K_CodeStep.pure_step]
  try simp only
  erw [F3K_CodeStep.lift_success _ _ access6]
  try simp only
  rw [h10]
  erw [F3K_CodeStep.pure_step,F3K_CodeStep.pure_step]
  erw [F3K_CodeBind.success _ _ _ r10]
  try simp only
  erw [F3K_CodeStep.pure_step]
  try simp only
  erw [F3K_CodeStep.lift_success _ _ access7]
  try simp only
  rw [h11]
  erw [F3K_CodeStep.pure_step,F3K_CodeStep.pure_step]
  erw [F3K_CodeBind.success _ _ _ r11]
  try simp only
  erw [F3K_CodeStep.pure_step]
  try simp only
  erw [F3K_CodeStep.lift_success _ _ access8]
  try simp only
  rw [h12]
  erw [F3K_CodeStep.pure_step,F3K_CodeStep.pure_step]
  erw [F3K_CodeBind.success _ _ _ r12]
  try simp only
  erw [F3K_CodeStep.pure_step]
  try simp only
  erw [F3K_CodeStep.lift_success _ _ access9]
  try simp only
  rw [← same13]
  rw [F3R_Begin13.log c13 c14 row13 row14 same14]
  rw [← same10]
  rw [← same11]
  rw [← same12]
  rw [F3J_ValidatedLog.semantic c9 (by rw [row9];decide)]
  rw [F3J_ValidatedLog.semantic c10 (by rw [row10];decide)]
  rw [F3J_ValidatedLog.semantic c11 (by rw [row11];decide)]
  rw [F3J_ValidatedLog.semantic c12 (by rw [row12];decide)]
  simp only [List.append_assoc]

#print axioms log
end AspisR1.F3R_Begin9
end
