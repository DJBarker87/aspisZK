import CuSavingsArrayGuard

/-! The emitted write step preserves the initialized-prefix invariant needed
by array::from_fn. This consumes source_success; it is not a proof of the
untranslated enclosing library loop or of the unsafe primitive models. -/
set_option autoImplicit false
set_option maxHeartbeats 100000
namespace AspisR1.CuSavingsArrayGuardPrefix
open Aeneas Aeneas.Std Result CuSavingsArrayGuard

def InitializedAs {T : Type} (self : Guard T) (values : List T) : Prop :=
  self.initialized.val = values.length ∧
  values.length ≤ self.array_mut.length ∧
  ∀ (j : Nat) (hj : j < values.length),
    self.array_mut.val[j]? = some (some (values[j]'hj))

theorem push_prefix {T : Type} (self : Guard T) (values : List T) (item : T)
    (hI : InitializedAs self values)
    (hroom : values.length < self.array_mut.length) :
    ∃ after : Guard T,
      AspisR1CuArraySource.core.array.Guard.push_unchecked self item =
        .ok (after,fun replacement : Guard T => {self with array_mut:=replacement.array_mut}) ∧
      InitializedAs after (values++[item]) ∧
      after.array_mut.length = self.array_mut.length := by
  rcases hI with ⟨hcount,hbound,hcells⟩
  have hindex : self.initialized.val < self.array_mut.length := by omega
  obtain ⟨next,hn,hexec⟩ := source_success self item hindex
  let after : Guard T :=
    {array_mut:=self.array_mut.set self.initialized (some item),initialized:=next}
  have hlen : after.array_mut.length = self.array_mut.length := by
    exact Slice.set_length _ _ _
  refine ⟨after,hexec,?_,hlen⟩
  refine ⟨?_,?_,?_⟩
  · change next.val = (values++[item]).length
    simp only [List.length_append,List.length_singleton,hn,hcount]
  · rw [List.length_append,List.length_singleton,hlen]
    omega
  · intro j hj
    change (self.array_mut.set self.initialized (some item)).val[j]? = _
    by_cases hleft : j < values.length
    · rw [frame self item j (by omega),hcells j hleft]
      simp only [List.getElem_append_left hleft]
    · have hjlast : j = self.initialized.val := by
        simp only [List.length_append,List.length_singleton] at hj
        omega
      subst j
      rw [written self item hindex]
      have helem : (values++[item])[self.initialized.val]'hj = item := by
        rw [hcount]
        simp
      rw [helem]

#print axioms InitializedAs
#print axioms push_prefix
end AspisR1.CuSavingsArrayGuardPrefix
