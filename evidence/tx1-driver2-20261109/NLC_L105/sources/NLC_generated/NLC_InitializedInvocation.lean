import NLC_SourceActual
import NLC_SourceInvocation
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLC_Finish
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
/-- Every visited source-interpreter state retains its initialized slots and
is a major state. The unsupported nested-marker dispatcher arms are excluded. -/
def AllInitialized {H : Type} : {n : Nat} → {s : State H} →
 {out : Result (Out H)} → {log : PreparedHashCode.Log} → {events : List Event} →
 Invocation n s out log events → Prop
 | _,s,_,_,_,.returned _ => Ready s ∧ Major s
 | _,s,_,_,_,.next _ tail => Ready s ∧ Major s ∧ AllInitialized tail
 | _,s,_,_,_,.fail _ => Ready s ∧ Major s
 | _,s,_,_,_,.div _ => Ready s ∧ Major s

theorem initialized {H : Type} {n : Nat} {s : State H} {out : Result (Out H)}
 {log : PreparedHashCode.Log} {events : List Event} (cuts : Invocation n s out log events)
 (ready : Ready s) (major : Major s) : AllInitialized cuts := by
 revert ready major
 induction cuts with
 | returned head => intro ready major;exact ⟨ready,major⟩
 | next head tail ih =>
   intro ready major
   exact ⟨ready,major,ih (source_ready_next _ _ ready (congrArg Prod.snd head))
     (source_major_next _ _ major (congrArg Prod.snd head))⟩
 | fail head => intro ready major;exact ⟨ready,major⟩
 | div head => intro ready major;exact ⟨ready,major⟩
/-- Initialization is produced internally at the original inputs. This theorem
still does not identify the interpreter with adopted finish or native execution. -/
theorem initial_fold {H : Type} (input : Input H) :
 ∃ out log events, ∃ cuts : Invocation (fuel (initial input)) (initial input) out log events,
 AllInitialized cuts ∧ PreparedHashCode.run (fold (fuel (initial input)) (initial input)) = (log,out) := by
 obtain ⟨out,log,events,cuts⟩ := source_invocation (fuel (initial input)) (initial input) (Nat.le_refl _)
 have major : Major (initial input) := by change 0 < 32;decide
 exact ⟨out,log,events,cuts,initialized cuts (initial_ready input) major,fold_from_steps cuts⟩
#print axioms initialized
#print axioms initial_fold
#print initial_fold
end AspisR1.NLC_Finish
end
