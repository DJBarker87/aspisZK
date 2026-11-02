import PV_EVH_StackRegions
set_option autoImplicit false
namespace PV_EVH_EntropyRejectCleanup
open PV_EVH_StackZero (Slot State Cleared drop emitted)
open PV_EVH_StackRegions (Separate)
open PV_EVH_StackAdmission (HeapSeparate HeapCoherent)

/-- Frozen source's ordinary rejected-iteration scope order: leaf seed, field
entropy, original entropy. Successful moves take a different path. Actual
frame/key provenance and admission of all three slots remain P. -/
def cleanup (original field seed : Slot) (w : State) : State :=
  drop original (drop field (drop seed w))

def run (original field seed : Slot) : PV_EVH_StackCleanup.Q Unit := fun w =>
  ⟨.returned (.ok ()),cleanup original field seed w,
    emitted seed ++ emitted field ++ emitted original⟩

theorem all_cleared (original field seed : Slot) (w : State)
    (hof : Separate original field) (hos : Separate original seed)
    (hfs : Separate field seed) :
    Cleared original (cleanup original field seed w) ∧
    Cleared field (cleanup original field seed w) ∧
    Cleared seed (cleanup original field seed w) := by
  refine ⟨PV_EVH_StackZero.dropped_cleared original _,?_,?_⟩
  · exact PV_EVH_StackRegions.drop_keeps_clear original field _ hof
      (PV_EVH_StackZero.dropped_cleared field _)
  · exact PV_EVH_StackRegions.drop_keeps_clear original seed _ hos
      (PV_EVH_StackRegions.drop_keeps_clear field seed _ hfs
        (PV_EVH_StackZero.dropped_cleared seed w))

theorem runtime (original field seed : Slot) (w : State) :
    (cleanup original field seed w).frame.runtime = w.frame.runtime := by
  simp only [cleanup,PV_EVH_StackZero.dropped_runtime]

theorem heap_separate_after_drop (a b : Slot) (w : State)
    (h : HeapSeparate a w) : HeapSeparate a (drop b w) := by
  intro block hb i hi
  rw [PV_EVH_StackZero.dropped_runtime] at hb
  exact h block hb i hi

theorem heap_coherent (original field seed : Slot) (w : State)
    (hc : HeapCoherent w) (ho : HeapSeparate original w)
    (hf : HeapSeparate field w) (hs : HeapSeparate seed w) :
    HeapCoherent (cleanup original field seed w) := by
  exact PV_EVH_StackAdmission.drop_heap original _
    (PV_EVH_StackAdmission.drop_heap field _
      (PV_EVH_StackAdmission.drop_heap seed w hc hs)
      (heap_separate_after_drop field seed w hf))
    (heap_separate_after_drop original field _
      (heap_separate_after_drop original seed w ho))

/-- Retired physical slots are retained in source destruction order. This
does not remove their memory or assert erasure of moved/spilled copies. -/
theorem retired (original field seed : Slot) (w : State) :
    (cleanup original field seed w).frame.retired =
      original :: field :: seed :: w.frame.retired := by
  simp only [cleanup,PV_EVH_StackZero.retired_after_drop]

theorem history (original field seed : Slot) (w : State) :
    (cleanup original field seed w).history =
      ((w.history ++ (PV_EVH_ZeroizeArray.events seed.key 0 seed.initialized).map
        (PV_EVH_ZeroAddressBridge.physical seed.address)) ++
      (PV_EVH_ZeroizeArray.events field.key 0 field.initialized).map
        (PV_EVH_ZeroAddressBridge.physical field.address)) ++
      (PV_EVH_ZeroizeArray.events original.key 0 original.initialized).map
        (PV_EVH_ZeroAddressBridge.physical original.address) := by
  simp only [cleanup,PV_EVH_StackZero.dropped_history]

#print axioms all_cleared
#print axioms runtime
#print axioms heap_separate_after_drop
#print axioms heap_coherent
#print axioms retired
#print axioms history
end PV_EVH_EntropyRejectCleanup
