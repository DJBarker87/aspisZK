import NKE_Free
set_option autoImplicit false
noncomputable section
namespace NLT_Continuation
open Aeneas Aeneas.Std Result NKE_Free
/-- The actual decoded reply selects the continuation. Local is a relation of
entered and interpreted cuts, not a dictionary returning a seeded endpoint.
This generic algebra alone has no native-source credit. -/
inductive Invocation {E A : Type} (Local : E → E → Prop) :
 Program E A → Result A → List E → Prop where
 | ret (value : A) : Invocation Local (.ret value) (.ok value) []
 | prim_ok {B : Type} (value : B) (next : B → Program E A)
   (result : Result A) (events : List E) (tail : Invocation Local (next value) result events) :
   Invocation Local (.prim (.ok value) next) result events
 | prim_fail {B : Type} (error : Error) (next : B → Program E A) :
   Invocation Local (.prim (.fail error) next) (.fail error) []
 | prim_div {B : Type} (next : B → Program E A) :
   Invocation Local (.prim .div next) .div []
 | call_ok {B : Type} (codec : Codec E B) (seed : Result B) (next : B → Program E A)
   (actual : E) (cut : Local (codec.encode seed) actual) (value : B)
   (decoded : codec.decode actual=some (.ok value)) (result : Result A) (events : List E)
   (tail : Invocation Local (next value) result events) :
   Invocation Local (.call codec seed next) result (actual::events)
 | call_fail {B : Type} (codec : Codec E B) (seed : Result B) (next : B → Program E A)
   (actual : E) (cut : Local (codec.encode seed) actual) (error : Error)
   (decoded : codec.decode actual=some (.fail error)) :
   Invocation Local (.call codec seed next) (.fail error) [actual]
 | call_div {B : Type} (codec : Codec E B) (seed : Result B) (next : B → Program E A)
   (actual : E) (cut : Local (codec.encode seed) actual)
   (decoded : codec.decode actual=some .div) :
   Invocation Local (.call codec seed next) .div [actual]
/-- Forward association from the cuts. Both sides use the SAME continuation;
there is no equality of independent logs or parent endpoints as an input. -/
theorem source {E A : Type} (Local : E → E → Prop) (p : Program E A)
 (cuts : ∀ e∈(eval p).events,∀ actual,Local e actual → actual=e)
 (result : Result A) (events : List E) (native : Invocation Local p result events) :
 result=(eval p).result ∧ events=(eval p).events := by
 induction native with
 | ret value => exact ⟨rfl,rfl⟩
 | prim_ok value next result events tail ih => exact ih cuts
 | prim_fail error next => exact ⟨rfl,rfl⟩
 | prim_div next => exact ⟨rfl,rfl⟩
 | call_ok codec seed next actual cut value decoded result events tail ih =>
   have same:=cuts (codec.encode seed) (by cases seed <;> exact List.mem_cons_self) actual cut
   rw [same,codec.roundtrip] at decoded
   cases decoded
   have rest:=ih (fun e he actual localCut=>cuts e (List.mem_cons_of_mem _ he) actual localCut)
   exact ⟨rest.1,by simpa only [eval,same,List.cons.injEq] using rest.2⟩
 | call_fail codec seed next actual cut error decoded =>
   have same:=cuts (codec.encode seed) (by cases seed <;> exact List.mem_cons_self) actual cut
   rw [same,codec.roundtrip] at decoded
   cases decoded
   exact ⟨rfl,by simp only [eval,same]⟩
 | call_div codec seed next actual cut decoded =>
   have same:=cuts (codec.encode seed) (by cases seed <;> exact List.mem_cons_self) actual cut
   rw [same,codec.roundtrip] at decoded
   cases decoded
   exact ⟨rfl,by simp only [eval,same]⟩
#print source
#print axioms source
end NLT_Continuation
