import R1Z.PV_CB3_TransportMembership
set_option autoImplicit false
namespace R1Z.PV_CB3_TransportNodup
open PV_CB3_TransportOrder

theorem «prefix» (pivot : Nat) (pads : List Nat) (hn : pads.Nodup) :
    (pads ++ (List.range pivot).filter (fun r => !(pads.contains r))).Nodup := by
  apply List.nodup_append.mpr
  refine ⟨hn,List.Sublist.nodup List.filter_sublist List.nodup_range,?_⟩
  intro a ha b hb hab
  subst b
  have hf := (List.mem_filter.mp hb).2
  simpa [ha] using hf

theorem order_nodup (pivot : Nat) (pads : List Nat) (hn : pads.Nodup)
    (hp : ∀ r, r ∈ pads → r < pivot) : (order pivot pads).Nodup := by
  unfold order
  apply List.nodup_append.mpr
  refine ⟨«prefix» pivot pads hn,by simp,?_⟩
  intro a ha b hb hab
  have hb' : b=pivot := by simpa using hb
  have ha' : a < pivot := by
    rcases List.mem_append.mp ha with ha|ha
    · exact hp a ha
    · exact List.mem_range.mp (List.mem_filter.mp ha).1
  omega
#print axioms «prefix»
#print axioms order_nodup
end R1Z.PV_CB3_TransportNodup
