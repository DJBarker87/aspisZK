import PV_L2E_ByteDecode
import PV_L2E_HostQuerySafety
set_option autoImplicit false
namespace PV_L2E_QueryCandidates
open PV_L2D_QueryScan PV_L2D_QueryBounds

/-- Eight 32-bit words per raw 32-byte digest block, preserving all unused
suffixes. The source's bit-mask-to-remainder association remains explicit. -/
def blockWords (b : Nat → Nat) : List Nat :=
  (PV_L2E_ByteDecode.words b 0 8).map (fun w => w%262144)

def candidates (blocks : List (Nat → Nat)) : List Nat := blocks.flatMap blockWords

theorem block_length (b : Nat → Nat) : (blockWords b).length=8 := by
  simp only [blockWords,List.length_map,PV_L2E_ByteDecode.length]

theorem length (blocks : List (Nat → Nat)) : (candidates blocks).length=8*blocks.length := by
  induction blocks with
  | nil => rfl
  | cons b bs ih => simp only [candidates,List.flatMap_cons,List.length_append,List.length_cons,block_length] at *; omega

theorem small (blocks : List (Nat → Nat)) : ∀ w∈candidates blocks,w<2^18 := by
  intro w hw
  obtain ⟨b,_,hb⟩ := List.mem_flatMap.mp hw
  obtain ⟨v,_,rfl⟩ := List.mem_map.mp hb
  exact Nat.mod_lt _ (by decide)

/-- On eight complete raw blocks, the host scanner has exactly its 64-word
input. Missing-word failure is impossible, but exhaustion is NOT excluded. -/
theorem no_missing (blocks : List (Nat → Nat)) (eight : blocks.length=8) :
    (PV_L2E_HostQuery.run ⟨[],0⟩ (candidates blocks)).1≠.missingWord := by
  apply PV_L2E_HostQueryValue.no_missing_word
  rw [length,eight]

theorem all_accesses_safe (blocks : List (Nat → Nat)) :
    ∀ e∈(PV_L2E_HostQuery.run ⟨[],0⟩ (candidates blocks)).2,
      PV_L2E_HostQuerySafety.Safe e :=
  PV_L2E_HostQuerySafety.run_safe _ _ initial (small blocks)

#print axioms block_length
#print axioms length
#print axioms small
#print axioms no_missing
#print axioms all_accesses_safe
end PV_L2E_QueryCandidates
