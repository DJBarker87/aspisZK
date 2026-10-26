import JFs_TX2_Iterator
set_option autoImplicit false
namespace AspisR1.JFs_TX2_BatchWindow
open Aeneas Aeneas.Std Result

theorem minimum (a b : Usize) :
    ∃ c, core.cmp.min core.cmp.OrdUsize a b=ok c ∧ c.val=min a.val b.val := by
  have spec : core.cmp.min core.cmp.OrdUsize a b ⦃ c => c.val=min a.val b.val ⦄ := by
    unfold core.cmp.min
    step*
    all_goals scalar_tac
  exact WP.spec_imp_exists spec

theorem zero : JFs_TX2_ArrayEight.Bound (Array.repeat 8#usize 0#u64) 0 := by
  intro x hx
  change x∈List.replicate 8 (0#u64) at hx
  have same : x=0#u64 := (List.mem_replicate.mp hx).2
  subst x
  simp

theorem source (start : Usize) (bound : start.val<26) :
    ∃ end4 stop, start+4#usize=ok end4 ∧ core.cmp.min core.cmp.OrdUsize end4 26#usize=ok stop ∧
      start.val≤stop.val ∧ stop.val≤26 ∧ stop.val≤start.val+4 ∧ stop.val=min (start.val+4) 26 := by
  obtain ⟨end4,run,value⟩ := WP.spec_imp_exists (UScalar.add_spec (x:=start) (y:=4#usize) (by scalar_tac))
  obtain ⟨stop,hstop,vstop⟩ := minimum end4 26#usize
  have vs : stop.val=min (start.val+4) 26 := by simpa only [value,show (4#usize).val=4 from rfl,show (26#usize).val=26 from rfl] using vstop
  refine ⟨end4,stop,run,hstop,?_,?_,?_,vs⟩ <;> omega

#print axioms minimum
#print axioms zero
#print axioms source
end AspisR1.JFs_TX2_BatchWindow
