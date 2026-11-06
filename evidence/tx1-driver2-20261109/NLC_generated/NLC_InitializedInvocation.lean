import NLC_SourceActual
import NLC_SourceInvocation
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLC_Finish
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
open PreparedHashCode (Log run)
/-- Every visited interpreter state is initialized and major. This relation
has proof-valued elimination only; it makes no native association claim. -/
inductive InitializedInvocation {H : Type} : Nat → State H → Result (Out H) → Log → List Event → Prop where
 | returned {n : Nat} {s : State H} {out : Out H} {log : Log}
   (ready : Ready s) (major : Major s)
   (head : run (step s) = (log,ok (.inl out))) : InitializedInvocation (n+1) s (ok out) log [s.next]
 | next {n : Nat} {s after : State H} {out : Result (Out H)} {log suffix : Log} {events : List Event}
   (ready : Ready s) (major : Major s)
   (head : run (step s) = (log,ok (.inr after)))
   (tail : InitializedInvocation n after out suffix events) :
   InitializedInvocation (n+1) s out (log ++ suffix) (s.next :: events)
 | fail {n : Nat} {s : State H} {error : Error} {log : Log}
   (ready : Ready s) (major : Major s)
   (head : run (step s) = (log,fail error)) : InitializedInvocation (n+1) s (fail error) log [s.next]
 | div {n : Nat} {s : State H} {log : Log}
   (ready : Ready s) (major : Major s)
   (head : run (step s) = (log,div)) : InitializedInvocation (n+1) s div log [s.next]

theorem initialized {H : Type} {n : Nat} {s : State H} {out : Result (Out H)}
 {log : Log} {events : List Event} (cuts : Invocation n s out log events)
 (ready : Ready s) (major : Major s) : InitializedInvocation n s out log events := by
 revert ready major
 induction cuts with
 | returned head => intro ready major;exact .returned ready major head
 | next head tail ih =>
   intro ready major
   exact .next ready major head (ih (source_ready_next _ _ ready (congrArg Prod.snd head))
     (source_major_next _ _ major (congrArg Prod.snd head)))
 | fail head => intro ready major;exact .fail ready major head
 | div head => intro ready major;exact .div ready major head
/-- Initializations are produced internally. Equality with adopted finish and
native execution remain separate OPEN obligations. -/
theorem initial_fold {H : Type} (input : Input H) :
 ∃ out log events, InitializedInvocation (fuel (initial input)) (initial input) out log events ∧
 run (fold (fuel (initial input)) (initial input)) = (log,out) := by
 obtain ⟨out,log,events,cuts⟩ := source_invocation (fuel (initial input)) (initial input) (Nat.le_refl _)
 have major : Major (initial input) := by change 0 < 32;decide
 exact ⟨out,log,events,initialized cuts (initial_ready input) major,fold_from_steps cuts⟩
#print axioms initialized
#print axioms initial_fold
#print initial_fold
end AspisR1.NLC_Finish
end
