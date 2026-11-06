import NIW_AlignRegularPhaseSource
set_option autoImplicit false
noncomputable section
namespace AspisR1.NIW_AlignRegularTransitions
open Aeneas Aeneas.Std Result NIT_Cuts NIT_PairControl NIW_AlignRegularStream

def Adjacent (events : List Event) : Prop :=
 ∀ before first second after,events=before++first::second::after →
 first.outcome=ok (.Ok (),second.before,second.parts)

theorem head_state (ks : List Usize) (s : Scratch) (p : Parts) (events : List Event)
 (out : Result NHM_RegularKinds.Reply) (order : Ordered ks s p events out)
 (event : Event) (rest : List Event) (same : events=event::rest) : event.before=s ∧ event.parts=p := by
 cases order with
 | done s p => cases same
 | failed k ks s p err => cases (List.cons.inj same).1;exact ⟨rfl,rfl⟩
 | diverged k ks s p => cases (List.cons.inj same).1;exact ⟨rfl,rfl⟩
 | rejected k ks s after p post err => cases (List.cons.inj same).1;exact ⟨rfl,rfl⟩
 | continued k ks s after p post events out tail => cases (List.cons.inj same).1;exact ⟨rfl,rfl⟩

theorem short (events : List Event) (small : events.length≤1) : Adjacent events := by
 intro before first second after same
 have sizes := congrArg List.length same
 simp only [List.length_append,List.length_cons] at sizes
 omega

theorem ordered (ks : List Usize) (s : Scratch) (p : Parts) (events : List Event)
 (out : Result NHM_RegularKinds.Reply) (order : Ordered ks s p events out) : Adjacent events := by
 induction order with
 | done s p => exact short [] (by simp)
 | failed k ks s p err => exact short _ (by simp)
 | diverged k ks s p => exact short _ (by simp)
 | rejected k ks s after p post err => exact short _ (by simp)
 | continued k ks s after p post events out tail ih =>
  intro before first second rest same
  cases before with
  | nil =>
   have identities := List.cons.inj same
   have frames := head_state ks after post events out tail second rest identities.2
   rw [←identities.1,frames.1,frames.2]
  | cons head before =>
   have history := (List.cons.inj same).2
   exact ih before first second rest history

theorem source [FIo_Native.Allocation] (c : Context) (before : Scratch) :
 Adjacent (NIW_AlignRegularPhase.run c before).2.events := by
 rw [NIW_AlignRegularPhaseSource.events]
 exact ordered _ _ _ _ _ (NIW_AlignRegularInvocation.ordered c.w.value c.alpha.value.to_slice
  c.f.value c.ap0.value c.ap1.value _ before initial)

#print axioms head_state
#print axioms short
#print axioms ordered
#print axioms source
end AspisR1.NIW_AlignRegularTransitions
