import Mathlib.Logic.Function.Basic
import Mathlib.Data.List.Basic
set_option autoImplicit false
namespace R1Z.PV_Inv_RawSlots
variable {V W : Type} [Zero W] [DecidableEq W]
structure Entry (V W : Type) where
  value : V
  weight : W
abbrev Slots (V W : Type) := Fin 2 → Entry V W

def put (s : Slots V W) (i : Fin 2) (e : Entry V W) : Slots V W := Function.update s i e

def step (s : Slots V W) (e : Entry V W) : Option (Slots V W) :=
  if (s 0).weight = 0 then some (put s 0 e)
  else if (s 1).weight = 0 then some (put s 1 e)
  else none

def Good (P : V → Prop) (s : Slots V W) : Prop := ∀ i, (s i).weight ≠ 0 → P (s i).value

theorem put_good (P : V → Prop) (s : Slots V W) (i : Fin 2) (e : Entry V W)
    (hs : Good P s) (he : P e.value) : Good P (put s i e) := by
  intro j hj
  by_cases h : j=i
  · subst j; simpa [put] using he
  · simpa [put,h] using hs j (by simpa [put,h] using hj)

theorem step_good (P : V → Prop) (s t : Slots V W) (e : Entry V W)
    (hs : Good P s) (he : P e.value) (hr : step s e = some t) : Good P t := by
  unfold step at hr
  split at hr
  · cases hr; exact put_good P s 0 e hs he
  · split at hr
    · cases hr; exact put_good P s 1 e hs he
    · cases hr

#print axioms put_good
#print axioms step_good
end R1Z.PV_Inv_RawSlots
