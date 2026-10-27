import R1Z.PV_Inv_RawRun
import Mathlib.Data.Finset.Basic
set_option autoImplicit false
namespace R1Z.PV_Inv_RawInvoke
open PV_Inv_RawSlots
variable {V W : Type} [Zero W] [DecidableEq W]

def reached (s : Slots V W) : List V :=
  (List.ofFn s).filterMap (fun e => if e.weight=0 then none else some e.value)

theorem reached_good (P : V → Prop) (s : Slots V W) (hs : Good P s) : ∀ v ∈ reached s, P v := by
  intro v hv
  obtain ⟨e,he,hv⟩ := List.mem_filterMap.mp hv
  obtain ⟨i,hi⟩ := List.mem_ofFn.mp he
  subst e
  split at hv
  · cases hv
  · rename_i hn
    cases hv
    exact hs i hn

theorem reached_origin (s : Slots V W) (v : V) (hv : v ∈ reached s) :
    ∃ i, (s i).weight ≠ 0 ∧ (s i).value=v := by
  obtain ⟨e,he,hv⟩ := List.mem_filterMap.mp hv
  obtain ⟨i,hi⟩ := List.mem_ofFn.mp he
  subst e
  split at hv
  · cases hv
  · rename_i hn
    cases hv
    exact ⟨i,hn,rfl⟩

#print axioms reached_good
#print axioms reached_origin
end R1Z.PV_Inv_RawInvoke
