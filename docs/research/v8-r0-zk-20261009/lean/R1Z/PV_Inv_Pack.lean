import R1Z.PV_Inv_Guard
import Mathlib.Data.List.Defs

/-! Structural reference of pair_forest_trace's first-zero-weight slot packing.
A zero-weight endpoint may be overwritten; a reached weighted slot still
contains a registry endpoint, never a sum of endpoints. -/
set_option autoImplicit false
namespace R1Z.PV_Inv_Pack
variable {K : Type} [Field K] [DecidableEq K]
structure Endpoint (K : Type) where
  value : K
  weight : K
abbrev Slots (K : Type) := Fin 2 → Endpoint K

def put (s : Slots K) (i : Fin 2) (e : Endpoint K) : Slots K := Function.update s i e

def step (s : Slots K) (e : Endpoint K) : Option (Slots K) :=
  if (s 0).weight = 0 then some (put s 0 e)
  else if (s 1).weight = 0 then some (put s 1 e)
  else none

def Safe (chi : K) (s : Slots K) : Prop :=
  ∀ i, (s i).weight ≠ 0 → chi ≠ (s i).value

theorem put_safe (chi : K) (s : Slots K) (i : Fin 2) (e : Endpoint K)
    (hs : Safe chi s) (he : chi ≠ e.value) : Safe chi (put s i e) := by
  intro j hj
  by_cases hji : j=i
  · subst j
    simpa [put] using he
  · simpa [put,hji] using hs j (by simpa [put,hji] using hj)

theorem step_safe (chi : K) (s t : Slots K) (e : Endpoint K)
    (hs : Safe chi s) (he : chi ≠ e.value) (run : step s e = some t) : Safe chi t := by
  unfold step at run
  split at run
  · cases run
    exact put_safe chi s 0 e hs he
  · split at run
    · cases run
      exact put_safe chi s 1 e hs he
    · cases run

def empty : Slots K := fun _ => ⟨0,0⟩

theorem empty_safe (chi : K) : Safe chi (empty : Slots K) := by
  intro i h
  exact (h rfl).elim

#print axioms put_safe
#print axioms step_safe
#print axioms empty_safe
end R1Z.PV_Inv_Pack
