import NNG_LIBArrays
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_LIBArrayDomain
open Aeneas Aeneas.Std NNG_Emitted NNG_LIBScalar NNG_LIBArrays
open AspisR1.NMT_Transport (arr)
def DomainArray {n : Usize} (a : Array Raw n) : Prop := ∀ x ∈ a.val, Domain x

theorem lower_canonical {n : Usize} (a : Array Value n) : DomainArray (lowerArray a) := by
  intro x member
  obtain ⟨v,_,same⟩ := List.mem_map.mp member
  subst x
  exact lower_domain v
#print axioms lower_canonical

theorem lower_project_array {n : Usize} (fallback : Value) (a : Array Raw n) (h : DomainArray a) :
    lowerArray (projectArray fallback a) = a := by
  apply Subtype.ext
  change (a.val.map (project fallback)).map lower = a.val
  rw [List.map_map]
  calc
    a.val.map (lower ∘ project fallback) = a.val.map id := by
      apply List.map_congr_left
      intro x hx
      exact lower_project fallback x (h x hx)
    _ = a.val := List.map_id _
#print axioms lower_project_array

theorem get_domain {n : Usize} (a : Array Raw n) (h : DomainArray a) (i : Usize) (hi : i.val < n.val) :
    Domain (NNG_Array136.get a i hi) := by
  apply h
  exact List.getElem_mem _
#print axioms get_domain
end AspisR1.NNG_LIBArrayDomain
