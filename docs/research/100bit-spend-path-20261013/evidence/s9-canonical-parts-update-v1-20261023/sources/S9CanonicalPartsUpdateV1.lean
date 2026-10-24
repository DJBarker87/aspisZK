import S9ActualFinalSumV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1S9CanonicalPartsUpdateV1
open AspisR1S9NativeWideDecodedArithmeticV1
open AspisR1S9ActualFinalSumV1
open AspisR1S9FactorArrayEntryV1

/-- A same successful bounded source update preserves canonicality of every
read of the actual parts array. Other cells use the existing exact frame. -/
theorem update_preserves_good (parts out : A) (i : Usize) (value : W)
    (hi : i.val<7) (hp : Good parts) (hv : Canonical value)
    (hupdate : Array.update parts i value=.ok out) : Good out := by
  have hout := accepted_update_eq_set parts i hi value out hupdate
  subst out
  intro j w hread
  have hj := AspisR1S9ConstructorV3Loop2InnerCanonicalV1.index_success_bound
    (parts.set i value) j w hread
  have hw := accepted_index_eq_atN (parts.set i value) j hj w hread
  rw [atN_set parts i j value hi hj] at hw
  by_cases hji : j.val=i.val
  · rw [if_pos hji] at hw
    rw [hw]
    exact hv
  · rw [if_neg hji] at hw
    rw [hw]
    exact hp j (atN parts j hj) (index_atN parts j hj)

#print axioms update_preserves_good
end AspisR1S9CanonicalPartsUpdateV1
