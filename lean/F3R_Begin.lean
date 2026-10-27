import F3R_Begin5
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3R_Begin
open Aeneas Aeneas.Std Result
open AspisR1PublicPreparation PreparedHashCode SourceDigestLog
attribute [local irreducible] S1SemanticCode.semanticValidated S1SemanticCode.begin5

theorem log {Hash : Type} {D : aspis_core.Digest32 Hash} {pre : r1_wire.Prefix}
    (c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 : SourceFull25.Call D pre)
    (row0 : c0.row=0#u8)
    (row1 : c1.row=1#u8)
    (row2 : c2.row=2#u8)
    (row3 : c3.row=3#u8)
    (row4 : c4.row=4#u8)
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
    (same1 : c1.before=c0.after)
    (same2 : c2.before=c1.after)
    (same3 : c3.before=c2.after)
    (same4 : c4.before=c3.after)
    (same5 : c5.before=c4.after)
    (same6 : c6.before=c5.after)
    (same7 : c7.before=c6.after)
    (same8 : c8.before=c7.after)
    (same9 : c9.before=c8.after)
    (same10 : c10.before=c9.after)
    (same11 : c11.before=c10.after)
    (same12 : c12.before=c11.after)
    (same13 : c13.before=c12.after)
    (same14 : c14.before=c13.after)
    : observe (run (S1SemanticCode.begin D pre c0.before)).1=
      callLog c0++callLog c1++callLog c2++callLog c3++callLog c4++callLog c5++callLog c6++callLog c7++callLog c8++callLog c9++callLog c10++callLog c11++callLog c12++callLog c13++callLog c14 := by
  have h0 := c0.validated
  rw [row0] at h0
  have r0 := F3R_SemanticStep.returned c0 (by rw [row0];decide)
  have h1 := c1.validated
  rw [row1] at h1
  have r1 := F3R_SemanticStep.returned c1 (by rw [row1];decide)
  rw [same1] at r1
  have h2 := c2.validated
  rw [row2] at h2
  have r2 := F3R_SemanticStep.returned c2 (by rw [row2];decide)
  rw [same2] at r2
  have h3 := c3.validated
  rw [row3] at h3
  have r3 := F3R_SemanticStep.returned c3 (by rw [row3];decide)
  rw [same3] at r3
  have h4 := c4.validated
  rw [row4] at h4
  have r4 := F3R_SemanticStep.returned c4 (by rw [row4];decide)
  rw [same4] at r4
  obtain ⟨old0,back0,access0⟩ := F3R_ArrayAccess.total
    (Array.repeat 10#usize aspis_core.field.QM31.ZERO) 0#usize (by decide)
  obtain ⟨old1,back1,access1⟩ := F3R_ArrayAccess.total (back0 c3.q) 1#usize (by decide)
  unfold S1SemanticCode.begin
  rw [h0]
  erw [F3K_CodeStep.pure_step,F3K_CodeStep.pure_step]
  erw [F3K_CodeBind.success _ _ _ r0]
  try simp only
  erw [F3K_CodeStep.pure_step]
  try simp only
  rw [h1]
  erw [F3K_CodeStep.pure_step,F3K_CodeStep.pure_step]
  erw [F3K_CodeBind.success _ _ _ r1]
  try simp only
  erw [F3K_CodeStep.pure_step]
  try simp only
  rw [h2]
  erw [F3K_CodeStep.pure_step,F3K_CodeStep.pure_step]
  erw [F3K_CodeBind.success _ _ _ r2]
  try simp only
  erw [F3K_CodeStep.pure_step]
  try simp only
  rw [h3]
  erw [F3K_CodeStep.pure_step,F3K_CodeStep.pure_step]
  erw [F3K_CodeBind.success _ _ _ r3]
  try simp only
  erw [F3K_CodeStep.pure_step]
  try simp only
  erw [F3K_CodeStep.lift_success _ _ access0]
  try simp only
  rw [h4]
  erw [F3K_CodeStep.pure_step,F3K_CodeStep.pure_step]
  erw [F3K_CodeBind.success _ _ _ r4]
  try simp only
  erw [F3K_CodeStep.pure_step]
  try simp only
  erw [F3K_CodeStep.lift_success _ _ access1]
  try simp only
  rw [← same5]
  rw [F3R_Begin5.log c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 row5 row6 row7 row8 row9 row10 row11 row12 row13 row14 same6 same7 same8 same9 same10 same11 same12 same13 same14]
  rw [← same1]
  rw [← same2]
  rw [← same3]
  rw [← same4]
  rw [F3J_ValidatedLog.semantic c0 (by rw [row0];decide)]
  rw [F3J_ValidatedLog.semantic c1 (by rw [row1];decide)]
  rw [F3J_ValidatedLog.semantic c2 (by rw [row2];decide)]
  rw [F3J_ValidatedLog.semantic c3 (by rw [row3];decide)]
  rw [F3J_ValidatedLog.semantic c4 (by rw [row4];decide)]
  simp only [List.append_assoc]

#print axioms log
end AspisR1.F3R_Begin
end
