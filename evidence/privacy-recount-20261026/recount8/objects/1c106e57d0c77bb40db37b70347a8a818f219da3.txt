import R1Z.PV_RunJoin_RoundTableTrace

/-! Bounds of the actual finite round tables. Only small literal tables and
scalar comparisons are inspected; no permutation is evaluated. -/
set_option autoImplicit false
namespace R1Z.PV_RunJoin_RoundTableFacts
open Aeneas Aeneas.Std Result
open BuilderForestAdmissionPort PV_Src_PortSboxStep
open PV_RunJoin_EnumerateTrace

def initials := labels 0#usize poseidon2.EXTERNAL_INITIAL.val
def internals := labels 0#usize poseidon2.INTERNAL.val
def finals := labels 0#usize poseidon2.EXTERNAL_FINAL.val

theorem initials_canonical (p : Usize × State) (hp : p ∈ initials) : Canonical p.2 := by
  simp only [initials,poseidon2.EXTERNAL_INITIAL,Array.make,labels,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl
  all_goals
    intro j
    fin_cases j <;> decide
#print axioms initials_canonical

theorem finals_canonical (p : Usize × State) (hp : p ∈ finals) : Canonical p.2 := by
  simp only [finals,poseidon2.EXTERNAL_FINAL,Array.make,labels,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl
  all_goals
    intro j
    fin_cases j <;> decide
#print axioms finals_canonical

theorem internals_canonical (p : Usize × U32) (hp : p ∈ internals) : p.2.val < 2147483647 := by
  simp only [internals,poseidon2.INTERNAL,Array.make,labels,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide
#print axioms internals_canonical

end R1Z.PV_RunJoin_RoundTableFacts
