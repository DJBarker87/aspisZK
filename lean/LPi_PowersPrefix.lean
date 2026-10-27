import LPi_PowersStep
set_option autoImplicit false
namespace AspisR1.LPi_PowersPrefix
open Aeneas Aeneas.Std Result LPi_FieldValues

def power (x : EW) : Nat → EW
  | 0 => ew FIo_Native.aspis_core.field.wide_exact.WideExact.ONE
  | n+1 => mulE (power x n) x

def Holds {N : Usize} (a : Array NE N) (x : EW) (n : Nat) : Prop :=
  ∀ j, j < n → ∃ z, a.val[j]?=some z ∧ canonE z ∧ ew z=power x j

theorem advance {N : Usize} (a : Array NE N) (x : EW) (i : Usize) (p : NE)
    (hi : i.val < N.val) (hold : Holds a x i.val) (hp : canonE p)
    (value : ew p=power x i.val) : Holds (a.set i p) x (i.val+1) := by
  intro j hj
  have hlen : i.val < a.val.length := by simpa only [a.property] using hi
  by_cases hji : j=i.val
  · subst j
    refine ⟨p,?_,hp,value⟩
    simp [Array.set,List.getElem?_set,hlen,hi]
  · have hj0 : j < i.val := by omega
    obtain ⟨z,hz,hc,hv⟩ := hold j hj0
    refine ⟨z,?_,hc,hv⟩
    simpa [Array.set,List.getElem?_set,hji,Ne.symm hji] using hz

#print axioms advance
end AspisR1.LPi_PowersPrefix
