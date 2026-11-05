import NIT_FinishComposition
set_option autoImplicit false
namespace AspisR1.NIT_ResultChain
open Aeneas Aeneas.Std Result NIT_Cuts NIT_FinishComposition

/-- One entered call, with an exact local reply law and only reached
continuations. Abort constructors contain no observations of later calls. -/
inductive Trace {A B : Type} (call : Result (Reply A))
 (nextTrace : A → Result (Reply B) → Prop) : Result (Reply B) → Prop
 | failed (e : Error) (law : call=fail e) : Trace call nextTrace (fail e)
 | diverged (law : call=div) : Trace call nextTrace div
 | rejected (e : AspisR1Stage2.verifier.Error) (law : call=ok (.Err e)) :
   Trace call nextTrace (ok (.Err e))
 | returned (value : A) (out : Result (Reply B))
   (law : call=ok (.Ok value)) (tail : nextTrace value out) : Trace call nextTrace out

theorem interpreted {A B : Type} (call : Result (Reply A))
 (next : A → Result (Reply B)) (nextTrace : A → Result (Reply B) → Prop)
 (tailLaw : ∀ value out,nextTrace value out → next value=out)
 (out : Result (Reply B)) (trace : Trace call nextTrace out) : fullBind call next=out := by
 cases trace with
 | failed e law=>rw [law];rfl
 | diverged law=>rw [law];rfl
 | rejected e law=>rw [law];rfl
 | returned value out law tail=>simp only [fullBind,law,bind_tc_ok];exact tailLaw value out tail

/-- Completeness needs a continuation only after an actual successful reply;
it cannot turn a failed or diverged child into a returning native log. -/
theorem complete {A B : Type} (call : Result (Reply A))
 (nextTrace : A → Result (Reply B) → Prop)
 (tailExists : ∀ value,call=ok (.Ok value) → ∃ out,nextTrace value out) :
 ∃ out,Trace call nextTrace out := by
 cases h : call with
 | fail e=>exact ⟨fail e,.failed e rfl⟩
 | div=>exact ⟨div,.diverged rfl⟩
 | ok reply=>
  cases reply with
  | Err e=>exact ⟨ok (.Err e),.rejected e rfl⟩
  | Ok value=>
   obtain ⟨out,tail⟩:=tailExists value h
   exact ⟨out,.returned value out rfl tail⟩

/-- Result encoding commutes with each returning bind exactly; this is not an
assumption that the pair or the finish result is successful. -/
theorem returning_bind {A B : Type} (reply : Reply A) (next : A → Reply B) :
 fullBind (ok reply) (fun value=>ok (next value))=ok (rbind reply next) := by
 cases reply <;> rfl

#print axioms interpreted
#print axioms complete
#print axioms returning_bind
end AspisR1.NIT_ResultChain
