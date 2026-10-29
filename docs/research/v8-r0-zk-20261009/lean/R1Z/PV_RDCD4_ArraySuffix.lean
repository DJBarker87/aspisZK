import R1Z.PV_RDCD4_ArrayIter194
namespace R1Z.PV_RDCD4_ArraySuffix
open PV_RDCD4_ArrayIter194
set_option autoImplicit false

/-- Forward-only projection. stop never changes in this caller. -/
def remaining {E : Type} (s : State E) : List E := s.data.drop s.start

theorem active {E : Type} (s : State E) (stop : s.stop=s.data.length)
    (h : s.start<s.stop) :
    ∃ x, remaining s=x::remaining {s with start:=s.start+1} ∧
      next s=(some x,{s with start:=s.start+1}) := by
  have hi : s.start<s.data.length := by omega
  refine ⟨s.data[s.start], ?_, ?_⟩
  · exact List.drop_eq_getElem_cons hi
  · simp only [next,show 0<s.stop-s.start by omega,if_pos,
      List.getElem?_eq_getElem hi]

theorem done {E : Type} (s : State E) (h : s.start=s.stop)
    (stop : s.stop=s.data.length) :
    remaining s=[] ∧ next s=(none,s) := by
  constructor
  · simp only [remaining,h,stop,List.drop_length]
  · exact next_done s h

theorem new_remaining {E : Type} (xs : List E) : remaining (new xs)=xs := by
  exact List.drop_zero

#print axioms active
#print axioms done
#print axioms new_remaining
end R1Z.PV_RDCD4_ArraySuffix
