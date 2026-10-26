import F3R_SemanticChain
import S1SemanticCodeBeginV1
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3R_Begin13
open Aeneas Aeneas.Std Result
open AspisR1PublicPreparation PreparedHashCode SourceDigestLog
attribute [local irreducible] S1SemanticCode.semanticValidated

theorem log {Hash : Type} {D : aspis_core.Digest32 Hash} {pre : r1_wire.Prefix}
    (a b : SourceFull25.Call D pre) (rowa : a.row=13#u8) (rowb : b.row=14#u8)
    (same : b.before=a.after) (v0 v1 v2 v12 : aspis_core.field.QM31)
    (back : aspis_core.field.QM31 → Array aspis_core.field.QM31 10#usize) :
    observe (run (S1SemanticCode.begin13 D pre a.before v0 v1 v2 v12 back)).1=
      callLog a++callLog b := by
  have ha := a.validated
  have hb := b.validated
  rw [rowa] at ha
  rw [rowb] at hb
  have ra := F3R_SemanticStep.returned a (by rw [rowa];decide)
  have rb := F3R_SemanticStep.returned b (by rw [rowb];decide)
  rw [same] at rb
  unfold S1SemanticCode.begin13
  rw [ha]
  erw [F3K_CodeStep.pure_step,F3K_CodeStep.pure_step]
  erw [F3K_CodeBind.success _ _ _ ra]
  try simp only
  erw [F3K_CodeStep.pure_step]
  rw [hb]
  erw [F3K_CodeStep.pure_step,F3K_CodeStep.pure_step]
  erw [F3K_CodeBind.success _ _ _ rb]
  try simp only
  erw [F3K_CodeStep.pure_step]
  try simp only
  rw [← same]
  change observe (run (S1SemanticCode.semanticValidated D a.before a.record)).1 ++
    (observe (run (S1SemanticCode.semanticValidated D b.before b.record)).1 ++ [])=_
  rw [F3J_ValidatedLog.semantic a (by rw [rowa];decide),
    F3J_ValidatedLog.semantic b (by rw [rowb];decide),List.append_nil]

#print axioms log
end AspisR1.F3R_Begin13
end
