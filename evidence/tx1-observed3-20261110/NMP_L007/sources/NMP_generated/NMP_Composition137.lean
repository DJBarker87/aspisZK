import NMP_Transcription137
set_option autoImplicit false
noncomputable section
namespace AspisR1.NMP_Composition137
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
open PreparedHashCode (run)
open NMP_Transcription137
/-- Value/log agreement only. This is deliberately NOT a resource RowSpec. -/
structure ValueAgreement {H : Type} (a b : Cuts H) : Prop where
 parse : run a.parse = run b.parse
 mark0 : run a.mark0 = run b.mark0
 publicTranscript : ∀ p, run (a.publicTranscript p) = run (b.publicTranscript p)
 begin : ∀ p t, run (a.begin p t) = run (b.begin p t)
 mark1 : run a.mark1 = run b.mark1
 finish : ∀ p t c, run (a.finish p t c) = run (b.finish p t c)
/-- Parametric fold; the child's law is never encoded in a Rust stub. -/
theorem fold {H : Type} (a b : Cuts H) (h : ValueAgreement a b) :
 run (code a) = run (code b) := by
 unfold code
 apply NMP_CutAlgebra.congr_run _ _ _ _ h.parse
 intro p
 cases p with
 | Err e => rfl
 | Ok p =>
  apply NMP_CutAlgebra.congr_run _ _ _ _ h.mark0
  intro _
  apply NMP_CutAlgebra.congr_run _ _ _ _ (h.publicTranscript p)
  intro t
  cases t with
  | Err e => rfl
  | Ok t =>
   apply NMP_CutAlgebra.congr_run _ _ _ _ (h.begin p t)
   intro pair
   rcases pair with ⟨r,after⟩
   cases r with
   | Err e => rfl
   | Ok c =>
    apply NMP_CutAlgebra.congr_run _ _ _ _ h.mark1
    intro _
    exact h.finish p after c
#print axioms fold
#print fold
end AspisR1.NMP_Composition137
end
