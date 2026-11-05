import NIW_AlignFinishComposed
set_option autoImplicit false
noncomputable section
namespace AspisR1.NIW_AlignFinishComposedLog
open Aeneas Aeneas.Std Result NIT_Cuts AspisR1Stage2
open NIW_AlignFinishComposed

abbrev SourceObserved (A : Type) := NIW_AlignFinishExecution.Observed A

def forget {A : Type} (observed : Observed A) : SourceObserved A := (observed.1,observed.2.1)

theorem forget_observe {A B : Type} (call : Result (Reply A)) (event : Result (Reply A) → Event)
 (next : A → Observed B) :
 forget (observe call event next)=NIW_AlignFinishExecution.observe call event (fun value=>forget (next value)) := by
 cases call with
 | fail err => rfl
 | div => rfl
 | ok reply => cases reply <;> rfl

theorem forget_attach (info : PairInfo) (tail : Observed Unit) : forget (attach info tail)=forget tail := rfl

theorem observe_congr {A B : Type} (call : Result (Reply A)) (event : Result (Reply A) → Event)
 (f g : A → SourceObserved B) (same : ∀ value,call=ok (.Ok value) → f value=g value) :
 NIW_AlignFinishExecution.observe call event f=NIW_AlignFinishExecution.observe call event g := by
 cases call with
 | fail err => rfl
 | div => rfl
 | ok reply =>
  cases reply with
  | Err err => rfl
  | Ok value => simp only [NIW_AlignFinishExecution.observe,same value rfl]

/-- The entire chronological source log, not just the endpoint, is unchanged
when pair is replaced by its actual collected invocation certificate. -/
theorem source (r : NP6_StdModel.Reservation) (loc : Locations) (proof : Slice U8)
 (v : verifier.View) (p : verifier.Prepared) (a : verifier.Accumulator)
 (domain : NIG_FinishInput.Domain proof v p a) :
 forget (run r loc v p a)=NIW_AlignFinishExecution.run r v p a := by
 rw [run,forget_observe,NIW_AlignFinishExecution.run]
 apply observe_congr
 intro first firstCall
 rw [forget_observe]
 apply observe_congr
 intro claim claimCall
 rw [forget_observe]
 apply observe_congr
 intro owner newCall
 have caller := NIT_PairDomain.caller r proof v p a domain owner newCall
 have native := (NIW_AlignPairInstalled.source r ⟨loc.owner,owner⟩ ⟨loc.alpha,p.alpha⟩
  ⟨loc.message,v.final_message⟩ p.kappa loc.ap0 loc.ap1 loc.common loc.low loc.scratch loc.parts caller).1
 have pairLaw : NIT_ErrorTransport.full (detail r loc owner v p).native.1=
  FIo_Install.pair r owner p.alpha.to_slice v.final_message p.kappa := native.symm
 dsimp only
 rw [forget_attach,forget_observe,pairLaw,NIG_PairInputs.alpha_prefix]
 apply observe_congr
 intro value pairCall
 split
 · rfl
 · rw [forget_observe]
   apply observe_congr
   intro actual dotCall
   rfl

#print axioms forget_observe
#print axioms forget_attach
#print axioms observe_congr
#print axioms source
end AspisR1.NIW_AlignFinishComposedLog
