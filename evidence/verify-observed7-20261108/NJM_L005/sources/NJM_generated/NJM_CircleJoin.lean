import NIX_DispatchRun
import NIX_DispatchCut
set_option autoImplicit false
noncomputable section
namespace AspisR1.NJM_CircleJoin
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
open PreparedHashCode (Code run)
abbrev Block := Array U8 32#usize
abbrev Point := aspis_core.circle.SecureCirclePoint

/-- Deterministic value of the already CLOSED sampler at exactly this block. -/
def point (b : Block) (row : FinishModel.CircleRow) : Point :=
 Classical.choose (show ∃ p,F3M_CircleSource.source b row=ok p from by
  obtain ⟨q,mapped,_,_,_,law⟩:=NIX_SamplerLaw.adopted b row
  exact ⟨_,law⟩)

theorem point_law (b : Block) (row : FinishModel.CircleRow) :
 F3M_CircleSource.source b row=ok (point b row) := Classical.choose_spec _

/-- Concrete continuation, with no arbitrary FinishModel dictionary. -/
def after {H : Type} (row : FinishModel.CircleRow)
 (pair : core.result.Result Block r1_wire.Error × r1_wire.SemanticTranscript H) :
 Code (core.result.Result Point r1_wire.Error × r1_wire.SemanticTranscript H) :=
 match pair.1 with
 | .Ok block => pure (.Ok (point block row),pair.2)
 | .Err error => pure (.Err error,pair.2)

/-- All returning child arms use the installed CLOSED sampler internally. -/
theorem continuation {H : Type} (B : FinishModel.Boundaries) (row : FinishModel.CircleRow)
 (pair : core.result.Result Block r1_wire.Error × r1_wire.SemanticTranscript H) :
 run (NIX_ValidatedCut.after (F3M_CircleSource.install B) row pair.2 pair.1)=run (after row pair) := by
 rcases pair with ⟨reply,t⟩
 cases reply with
 | Err error => rfl
 | Ok block =>
   simpa only [after,NGX_CodeTrace.pure_run] using
    NIX_DispatchRun.returned (F3M_CircleSource.install B) row t block (point block row) (point_law block row)

/-- A complete bind retains the child's ordered effects and outer aborts. -/
theorem append_continuation {H : Type} (B : FinishModel.Boundaries) (row : FinishModel.CircleRow)
 (log : PreparedHashCode.Log)
 (reply : Result (core.result.Result Block r1_wire.Error × r1_wire.SemanticTranscript H)) :
 NGX_RunBind.appendResult log reply (fun pair=>NIX_ValidatedCut.after (F3M_CircleSource.install B) row pair.2 pair.1)=
 NGX_RunBind.appendResult log reply (after row) := by
 cases reply with
 | fail e => rfl
 | div => rfl
 | ok pair => simp only [NGX_RunBind.appendResult,continuation]

#print axioms point_law
#print axioms continuation
#print axioms append_continuation
end AspisR1.NJM_CircleJoin
end
