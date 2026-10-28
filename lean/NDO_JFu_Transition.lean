import NDO_JFu_TransitionSteps
import NDO_JFu_TransitionArithmetic
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFu_Transition
open Aeneas Aeneas.Std Result FIq_Native
open pool_v1.pair_forest_semantic_terminal

theorem pool : Aeneas.Std.core.array.equality.PartialEqArray.ne Aeneas.Std.core.cmp.PartialEqU8
    JFu_PublicSemantic.value.transition.live_snapshot.pool JFu_PublicSemantic.value.pool=ok false := rfl

theorem domain : Aeneas.Std.core.array.equality.PartialEqArray.ne Aeneas.Std.core.cmp.PartialEqU8
    JFu_PublicSemantic.value.transition.live_snapshot.deployment_domain JFu_PublicSemantic.value.deployment_domain=ok false := rfl

theorem sequence : (JFu_PublicSemantic.value.transition.live_snapshot.sequence !=
    JFu_PublicSemantic.value.transition.live_snapshot.next_pair_index)=false := rfl

theorem next : U64.checked_add JFu_PublicSemantic.value.transition.live_snapshot.next_pair_index 1#u64=
    some JFu_PublicSemantic.value.transition.candidate_afterstate.next_pair_index := rfl

theorem source : validate_transition JFu_PublicSemantic.value=ok (.Ok ()) := by
  unfold validate_transition
  simp only [pool,domain,sequence,JFu_TransitionArithmetic.capacity,bind_tc_ok,
    Bool.false_eq_true,ite_false,ite_true]
  have bound : ¬(JFu_PublicSemantic.value.transition.live_snapshot.next_pair_index>=1048576#u64) := by
    change ¬(13#u64>=1048576#u64)
    scalar_tac
  rw [if_neg bound]
  rw [next]
  simp only [lift,bind_tc_ok]
  have same : Aeneas.Std.core.cmp.PartialEq.ne.trait_default
      (FIq_Native.core.option.Option.Insts.CoreCmpPartialEqOption Aeneas.Std.core.cmp.PartialEqU64)
      (some JFu_PublicSemantic.value.transition.candidate_afterstate.next_pair_index)
      (some JFu_PublicSemantic.value.transition.candidate_afterstate.next_pair_index)=ok false := rfl
  rw [same,bind_tc_ok]
  simp only [Bool.false_eq_true,ite_false]
  have carry : bounded_append_carry JFu_PublicSemantic.value.transition.live_snapshot.next_pair_index=ok 1#usize := JFu_TransitionArithmetic.carry
  rw [carry,bind_tc_ok]
  exact JFu_TransitionSteps.source

#print axioms pool
#print axioms domain
#print axioms sequence
#print axioms next
#print axioms source
end AspisR1.JFu_Transition
end
