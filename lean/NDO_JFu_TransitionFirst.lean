import NDO_JFu_PublicSemantic
import ExtractedMaskForwardRange
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFu_TransitionFirst
open Aeneas Aeneas.Std Result FIq_Native
open pool_v1.pair_forest_semantic_terminal

def r0 : core.ops.range.Range Usize := ⟨0#usize,20#usize⟩
def r1 : core.ops.range.Range Usize := ⟨1#usize,20#usize⟩

theorem next : Aeneas.Std.core.iter.range.IteratorRange.next Aeneas.Std.core.iter.range.StepUsize r0=ok (some 0#usize,r1) := by
  obtain ⟨r,call,start,finish,_⟩ := ExtractedMaskForwardRange.next_step r0 (by change 0<20;omega)
  have sameStart : r.start=1#usize := UScalar.eq_of_val_eq (by change r.start.val=1;change r.start.val=0+1 at start;omega)
  have same : r=r1 := by cases r;simp_all [r0,r1]
  simpa only [same,r0] using call

theorem step : validate_transition_loop JFu_PublicSemantic.value r0 1#usize=
    validate_transition_loop JFu_PublicSemantic.value r1 1#usize := by
  rw [validate_transition_loop,next,bind_tc_ok]
  simp only [Aeneas.Std.uncurry,
    if_neg (by scalar_tac : ¬(0#usize=1#usize)),
    if_pos (by scalar_tac : 0#usize<1#usize),bind_tc_ok]
  unfold empty_root pool_v1.pair_forest_semantic_terminal.constants.POOL_V1_PAIR_EMPTY_ROOTS_V1
  rfl

#print axioms next
#print axioms step
end AspisR1.JFu_TransitionFirst
end
