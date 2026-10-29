import PV_L2E_QueryCandidates
import PV_L2E_EagerPairs
set_option autoImplicit false
namespace PV_L2E_QueryWrapper
open PV_L2D_QueryScan PV_L2D_QueryBounds PV_L2E_HostQuery PV_L2E_QueryCandidates

def stateAfter {H : Type} (absorbed : H) (advance : Nat → H) : PV_L2E_HostQuery.Result → H
  | .ok _ k => advance k
  | .exhausted | .missingWord => absorbed

def run {H : Type} (absorbed : H) (advance : Nat → H) (blocks : List (Nat → Nat)) :
    PV_L2E_HostQuery.Result × H × List PV_L2E_HostQuery.Event :=
  let q := PV_L2E_HostQuery.run ⟨[],0⟩ (candidates blocks)
  (q.1,stateAfter absorbed advance q.1,q.2)

/-- The '?' failure does not commit any speculative advance to self.state. -/
theorem failure_state {H : Type} (absorbed : H) (advance : Nat → H)
    (blocks : List (Nat → Nat))
    (failure : (run absorbed advance blocks).1=.exhausted) :
    (run absorbed advance blocks).2.1=absorbed := by
  change stateAfter absorbed advance _=absorbed
  rw [show (PV_L2E_HostQuery.run ⟨[],0⟩ (candidates blocks)).1=.exhausted from failure]
  rfl

/-- A source success exposes exactly 22 queries and a valid advance index.
Exhaustion remains a possible full Result on the same 64-word domain. -/
theorem success_shape {H : Type} (absorbed : H) (advance : Nat → H)
    (blocks : List (Nat → Nat)) (eight : blocks.length=8) (qs : List Nat) (k : Nat)
    (success : (run absorbed advance blocks).1=.ok qs k) :
    qs.length=22 ∧ k<8 ∧ (run absorbed advance blocks).2.1=advance k := by
  have remaining : (⟨[],0⟩ : State).draws+(candidates blocks).length=64 := by rw [length,eight]
  have hr := PV_L2E_HostQueryValue.complete_result ⟨[],0⟩ (candidates blocks) remaining
  have admitted := scan_admitted ⟨[],0⟩ (candidates blocks) initial (small blocks)
  have success' : (PV_L2E_HostQuery.run ⟨[],0⟩ (candidates blocks)).1=.ok qs k := success
  rw [hr] at success'
  unfold PV_L2E_HostQueryValue.finish at success'
  split at success'
  · rename_i hlen
    cases success'
    refine ⟨hlen,?_,?_⟩
    · split_ifs
      · decide
      · have hd := admitted.2.2.2.1; omega
    · change stateAfter absorbed advance _=_
      rw [show (PV_L2E_HostQuery.run ⟨[],0⟩ (candidates blocks)).1=_ from success]
      rfl
  · contradiction

#print axioms failure_state
#print axioms success_shape
end PV_L2E_QueryWrapper
