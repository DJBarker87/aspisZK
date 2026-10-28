import NDO_JFu_TransitionShift
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFu_TransitionSecond
open Aeneas Aeneas.Std Result FIq_Native
open pool_v1.pair_forest_semantic_terminal

def r2 : core.ops.range.Range Usize := ⟨2#usize,20#usize⟩
def r3 : core.ops.range.Range Usize := ⟨3#usize,20#usize⟩

theorem next : Aeneas.Std.core.iter.range.IteratorRange.next Aeneas.Std.core.iter.range.StepUsize r2=ok (some 2#usize,r3) := by
  obtain ⟨r,call,start,finish,_⟩ := ExtractedMaskForwardRange.next_step r2 (by change 2<20;omega)
  have sameStart : r.start=3#usize := UScalar.eq_of_val_eq (by change r.start.val=3;change r.start.val=2+1 at start;omega)
  have same : r=r3 := by cases r;simp_all [r2,r3]
  simpa only [same,r2] using call

theorem step : validate_transition_loop JFu_PublicSemantic.value r2 1#usize=
    validate_transition_loop JFu_PublicSemantic.value r3 1#usize := by
  rw [validate_transition_loop,next,bind_tc_ok]
  simp only [Aeneas.Std.uncurry,
    if_neg (by scalar_tac : ¬(2#usize=1#usize)),
    if_neg (by scalar_tac : ¬(2#usize<1#usize))]
  have shifted : JFu_PublicSemantic.value.transition.live_snapshot.next_pair_index >>> 2#usize=ok 3#u64 :=
    JFu_TransitionShift.shift2
  rw [shifted,bind_tc_ok]
  have bit : lift (3#u64 &&& 1#u64)=ok 1#u64 := rfl
  rw [bit,bind_tc_ok]
  simp only [if_neg (by scalar_tac : ¬(1#u64=0#u64)),bind_tc_ok,Aeneas.Std.uncurry]
  rfl

#print axioms next
#print axioms step
end AspisR1.JFu_TransitionSecond
end
