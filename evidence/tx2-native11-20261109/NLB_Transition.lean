import NLB_State
set_option autoImplicit false
noncomputable section
namespace NLB_Parent
open Aeneas Aeneas.Std Result NKE_Free
/-- One transition preserves the entire caller continuation and the same
chronological prefix. This relation has no unrelated invocation/log input. -/
inductive Step {A : Type} (window : Event → Event) : State A → State A → Prop where
 | ret (value : A) (before : List Event) :
   Step window (.live (.ret value) before) (.done (.ok value) before)
 | prim_ok {B : Type} (value : B) (next : B → Program Event A) (before : List Event) :
   Step window (.live (.prim (.ok value) next) before) (.live (next value) before)
 | prim_fail {B : Type} (error : Error) (next : B → Program Event A) (before : List Event) :
   Step window (.live (.prim (.fail error) next) before) (.done (.fail error) before)
 | prim_div {B : Type} (next : B → Program Event A) (before : List Event) :
   Step window (.live (.prim .div next) before) (.done .div before)
 | call_ok {B : Type} (codec : Codec Event B) (seed : Result B)
   (next : B → Program Event A) (before : List Event) (value : B)
   (decoded : codec.decode (window (codec.encode seed))=some (.ok value)) :
   Step window (.live (.call codec seed next) before)
     (.live (next value) (before++[window (codec.encode seed)]))
 | call_fail {B : Type} (codec : Codec Event B) (seed : Result B)
   (next : B → Program Event A) (before : List Event) (error : Error)
   (decoded : codec.decode (window (codec.encode seed))=some (.fail error)) :
   Step window (.live (.call codec seed next) before)
     (.done (.fail error) (before++[window (codec.encode seed)]))
 | call_div {B : Type} (codec : Codec Event B) (seed : Result B)
   (next : B → Program Event A) (before : List Event)
   (decoded : codec.decode (window (codec.encode seed))=some .div) :
   Step window (.live (.call codec seed next) before)
     (.done .div (before++[window (codec.encode seed)]))
 | invalid {B : Type} (codec : Codec Event B) (seed : Result B)
   (next : B → Program Event A) (before : List Event)
   (decoded : codec.decode (window (codec.encode seed))=none) :
   Step window (.live (.call codec seed next) before)
     (.invalid (before++[window (codec.encode seed)]))

inductive Trace {A : Type} (window : Event → Event) : State A → State A → Prop where
 | refl (state : State A) : Trace window state state
 | next {s t u : State A} (head : Step window s t) (tail : Trace window t u) : Trace window s u

/-- Execution exists for arbitrary window replies, with no assumed source log,
child success, parent endpoint, or NoBad premise. -/
theorem execution {A : Type} (window : Event → Event) (p : Program Event A)
 (before : List Event) : Trace window (.live p before) (G window p before) := by
 induction p generalizing before with
 | ret value => exact .next (.ret value before) (.refl _)
 | prim actual next ih =>
   cases actual with
   | ok value => exact .next (.prim_ok value next before) (ih value before)
   | fail error => exact .next (.prim_fail error next before) (.refl _)
   | div => exact .next (.prim_div next before) (.refl _)
 | call codec seed next ih =>
   cases decoded : codec.decode (window (codec.encode seed)) with
   | none =>
     simp only [G,decoded]
     exact .next (.invalid codec seed next before decoded) (.refl _)
   | some result =>
     cases result with
     | ok value =>
       simp only [G,decoded]
       exact .next (.call_ok codec seed next before value decoded) (ih value _)
     | fail error =>
       simp only [G,decoded]
       exact .next (.call_fail codec seed next before error decoded) (.refl _)
     | div =>
       simp only [G,decoded]
       exact .next (.call_div codec seed next before decoded) (.refl _)
#print axioms execution
end NLB_Parent
