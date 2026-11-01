import NEI_LineActual
set_option autoImplicit false
noncomputable section
namespace NEI_LineBridge
open Aeneas Aeneas.Std Result NEI_FieldCarriers NEI_LineActual
open AspisR1PublicPreparation.RawExtractedSemanticCallOpsV20
open AspisR1 AspisR1CurrentWide.Proof

/-- The actual extracted source uses identical fields; inverse is unrestricted. -/
def Domain (alpha : N.E) (a : Array N.E 4#usize) : Prop :=
  NEI_LineDomains.Domain (toE alpha) (rows a)

theorem returns (alpha : N.E) (a : Array N.E 4#usize) (inverse : Array U32 5#usize)
    (domain : Domain alpha a) :
    ∃ out, NEI_LineFull.line_fold_with_inverses alpha a inverse = ok out ∧
      NEG_FoldsTypes.line_fold_with_inverses (toE alpha) (rows a) inverse = ok (toE out) ∧
      CanonicalWide (toE out) := by
  obtain ⟨value,cohort,canonical⟩ := NEI_LineDomains.total (toE alpha) (rows a) inverse domain
  have source : SAQ_LineSource.line (toE alpha) (rows a) inverse = ok value :=
    (NEG_FoldAssociation.line _ _ _).symm.trans cohort
  have mapped := (NEI_LineActual.body alpha a inverse).trans source
  cases native : NEI_LineFull.line_fold_with_inverses alpha a inverse with
  | fail e => simp only [native,resultMap] at mapped; cases mapped
  | div => simp only [native,resultMap] at mapped; cases mapped
  | ok out =>
    have same : toE out = value := by
      simp only [native,resultMap] at mapped
      exact Result.ok.inj mapped
    exact ⟨out,native,by simpa only [same] using cohort,by simpa only [same] using canonical⟩

/-- Full Result and the pure frame are from this same extracted execution. -/
theorem complete {S Event : Type} (state : S) (alpha : N.E)
    (a : Array N.E 4#usize) (inverse : Array U32 5#usize) (domain : Domain alpha a) :
    ∃ out, NEI_LineFull.line_fold_with_inverses alpha a inverse = ok out ∧
      CanonicalWide (toE out) ∧
      NEB_PureFrame.run (Event:=Event) state
        (NEI_LineFull.line_fold_with_inverses alpha a inverse) = ok (out,state,[]) ∧
      NEG_FoldsTypes.line_fold_with_inverses (toE alpha) (rows a) inverse = ok (toE out) := by
  obtain ⟨out,native,cohort,canonical⟩ := returns alpha a inverse domain
  exact ⟨out,native,canonical,NEB_PureFrame.successful state _ _ native,cohort⟩

#print axioms returns
#print axioms complete
end NEI_LineBridge
end
