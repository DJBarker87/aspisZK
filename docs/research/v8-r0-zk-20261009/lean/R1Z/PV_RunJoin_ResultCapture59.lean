import R1Z.PV_RunJoin_ResultPost
set_option autoImplicit false
namespace R1Z.PV_RunJoin_ResultCapture59
open Aeneas Aeneas.Std Result
open PV_RunJoin_ResultPost

theorem bind {A B : Type} (P : B → Prop) (m : Result A) (k : A → Result B)
    (continuation : ∀ a, m=ok a → Post P (k a)) : Post P (m >>= k) := by
  cases hm : m with
  | fail e => intro b h; cases h
  | div => intro b h; cases h
  | ok a => exact continuation a hm

theorem guard {A : Type} (P : A → Prop) (condition : Prop) [Decidable condition]
    (tail : Result A) (continuation : condition → Post P tail) :
    Post P (do massert condition; tail) := by
  unfold massert
  split
  · simpa only [bind_tc_ok] using continuation ‹condition›
  · intro b h; cases h

#print axioms bind
#print axioms guard
end R1Z.PV_RunJoin_ResultCapture59
