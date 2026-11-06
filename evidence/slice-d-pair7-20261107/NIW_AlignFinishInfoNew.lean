import NIW_AlignFinishInfoEvent
set_option autoImplicit false
noncomputable section
namespace AspisR1.NIW_AlignFinishInfoNew
open Aeneas Aeneas.Std Result NIT_Cuts AspisR1Stage2 NIW_AlignFinishComposed NIW_AlignFinishInfoEvent

def HasNew {A : Type} (p : verifier.Prepared) (observed : Observed A) : Prop :=
 ∀ info,observed.2.2=some info → ∃ before after,
 observed.2.1=before++(.new p (ok (.Ok info.owner.value)))::eventOf info::after

theorem head_suffix {A B : Type} (call : Result (Reply A)) (event : Result (Reply A) → Event)
 (next : A → Observed B) : ∃ tail,(observe call event next).2.1=event call::tail := by
 cases call with
 | fail err => exact ⟨[],rfl⟩
 | div => exact ⟨[],rfl⟩
 | ok reply => cases reply with
   | Err err => exact ⟨[],rfl⟩
   | Ok value => exact ⟨(next value).2.1,rfl⟩

theorem adjacent (p : verifier.Prepared) (info : PairInfo)
 (call : Result (Reply FE)) (event : Result (Reply FE) → Event) (next : FE → Observed Unit)
 (sameEvent : event call=eventOf info) :
 HasNew p (let tail:=observe call event next
  (tail.1,(.new p (ok (.Ok info.owner.value)))::tail.2.1,some info)) := by
 intro actual same
 have equal := Option.some.inj same
 subst actual
 obtain ⟨after,recorded⟩ := head_suffix call event next
 exact ⟨[],after,by simp only [recorded,sameEvent,List.nil_append]⟩

theorem preserve {A B : Type} (p : verifier.Prepared) (call : Result (Reply A))
 (event : Result (Reply A) → Event) (next : A → Observed B)
 (tail : ∀ value,call=ok (.Ok value) → HasNew p (next value)) : HasNew p (observe call event next) := by
 cases call with
 | fail err => intro info same;cases same
 | div => intro info same;cases same
 | ok reply =>
  cases reply with
  | Err err => intro info same;cases same
  | Ok value =>
   intro info same
   obtain ⟨before,after,history⟩ := tail value rfl info same
   exact ⟨event (ok (.Ok value))::before,after,by simp only [observe,history,List.cons_append]⟩

/-- The NEW event immediately preceding the pair event returns exactly the
owner stored in the nested actual pair certificate. All earlier aborts have
no pair certificate; no successful-NEW hypothesis is taken by this theorem. -/
theorem source (r : NP6_StdModel.Reservation) (loc : Locations)
 (v : verifier.View) (p : verifier.Prepared) (a : verifier.Accumulator) : HasNew p (run r loc v p a) := by
 unfold run
 apply preserve
 intro first firstCall
 apply preserve
 intro claim claimCall
 cases newCall : (NIG_Slots.installed r).op3 p.variant p.semantic_alpha p.z with
 | fail err => simp only [newCall,observe];intro info same;cases same
 | div => simp only [newCall,observe];intro info same;cases same
 | ok reply =>
  cases reply with
  | Err err => simp only [newCall,observe];intro info same;cases same
  | Ok owner =>
   simp only [newCall,observe,attach]
   exact adjacent p (detail r loc owner v p) _ _ _ rfl

#print axioms head_suffix
#print axioms adjacent
#print axioms preserve
#print axioms source
end AspisR1.NIW_AlignFinishInfoNew
