import NNG_TraceAll136
set_option autoImplicit false
namespace AspisR1.NNG_AllPlain136
open Aeneas Aeneas.Std Result NMT_CallTree NNG_TraceAll136

theorem plain {A B : Type} (P : Event → Prop) (r : Result A) (next : A → Code B)
    (tail : ∀ a,All P (next a)) : All P (.plain r next) := by
  intro e member
  cases r with
  | fail err => cases member
  | div => cases member
  | ok a => exact tail a e member
#print axioms plain
end AspisR1.NNG_AllPlain136
