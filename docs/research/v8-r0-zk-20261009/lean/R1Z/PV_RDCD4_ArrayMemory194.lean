import R1Z.PV_RDCD4_Memory194
import R1Z.PV_RDCD4_ArrayIter194
open Aeneas Aeneas.Std Result
namespace R1Z.PV_RDCD4_ArrayMemory194
set_option autoImplicit false

def source {E : Type} (origin : Nat) (s : PV_RDCD4_ArrayIter194.State E) :
    Result (Option E × PV_RDCD4_ArrayIter194.State E) := do
  if 0 < s.stop-s.start then
    let idx := s.start
    let s := {s with start := s.start+1}
    let value ← PV_RDCD4_Memory194.constPtrRead ⟨origin,s.data,idx⟩
    ok (some value,s)
  else ok (none,s)

/-- Store the advanced range before the initialized read, then restore all
fields. Failure of the raw-read model is excluded by the original live range. -/
theorem binding {E : Type} (origin : Nat) (s : PV_RDCD4_ArrayIter194.State E)
    (hv : PV_RDCD4_ArrayIter194.valid s) :
    source origin s=ok (PV_RDCD4_ArrayIter194.next s) := by
  by_cases ha : s.start < s.stop
  · have h : 0 < s.stop-s.start := by omega
    have hb : s.start < s.data.length := by obtain ⟨_,hb⟩ := hv; omega
    unfold source
    rw [if_pos h,PV_RDCD4_Memory194.read_at _ hb,bind_tc_ok]
    simp only [PV_RDCD4_ArrayIter194.next,if_pos h,List.getElem?_eq_getElem hb]
  · have h : ¬0 < s.stop-s.start := by omega
    simp only [source,if_neg h,PV_RDCD4_ArrayIter194.next,if_neg h]

#print axioms binding
end R1Z.PV_RDCD4_ArrayMemory194
