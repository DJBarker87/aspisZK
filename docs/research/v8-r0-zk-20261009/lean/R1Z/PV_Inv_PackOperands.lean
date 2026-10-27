import R1Z.PV_Inv_PackList
set_option autoImplicit false
namespace R1Z.PV_Inv_PackOperands
open PV_Inv_Pack PV_Inv_PackList
variable {K : Type} [Field K] [DecidableEq K]

def operands (chi : K) (s : Slots K) : List K :=
  (List.ofFn s).filterMap (fun e => if e.weight = 0 then none else some (chi-e.value))

theorem reached_nonzero (chi : K) (s : Slots K) (safe : Safe chi s) :
    ∀ d ∈ operands chi s, d ≠ 0 := by
  intro d hd
  obtain ⟨e,he,hd⟩ := List.mem_filterMap.mp hd
  obtain ⟨i,hi⟩ := List.mem_ofFn.mp he
  subst e
  split at hd
  · cases hd
  · rename_i hn
    cases hd
    exact sub_ne_zero.mpr (safe i hn)

theorem packed_nonzero (chi : K) (es : List (Endpoint K)) (s : Slots K)
    (hp : ∀ e ∈ es, chi ≠ e.value) (hr : run empty es = some s) :
    ∀ d ∈ operands chi s, d ≠ 0 :=
  reached_nonzero chi s (from_empty chi es s hp hr)

#print axioms reached_nonzero
#print axioms packed_nonzero
end R1Z.PV_Inv_PackOperands
