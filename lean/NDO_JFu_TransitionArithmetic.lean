import NDO_JFu_PublicSemantic
import NDO_JFr_IndexArithmetic
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFu_TransitionArithmetic
open Aeneas Aeneas.Std Result WP FIq_Native
open pool_v1.pair_forest_semantic_terminal

theorem capacity : pool_v1.pair_tree_profile.POOL_V1_PAIR_CAPACITY=ok 1048576#u64 := by
  unfold pool_v1.pair_tree_profile.POOL_V1_PAIR_CAPACITY
    pool_v1.pair_tree_profile.POOL_V1_PAIR_TREE_DEPTH pool_v1.format.POOL_V1_TREE_DEPTH
  have spec : (1#u64 <<< 20#usize : Result U64) ⦃ out => out.val=1048576 ⦄ := by
    step* <;> scalar_tac
  obtain ⟨out,call,value⟩ := WP.spec_imp_exists spec
  have same : out=1048576#u64 := UScalar.eq_of_val_eq value
  exact same ▸ call

theorem shift : (13#u64 >>> 1#u32 : Result U64)=ok 6#u64 := by
  have spec : (13#u64 >>> 1#u32 : Result U64) ⦃ out => out.val=6 ⦄ := by
    step* <;> scalar_tac
  obtain ⟨out,call,value⟩ := WP.spec_imp_exists spec
  have same : out=6#u64 := UScalar.eq_of_val_eq value
  exact same ▸ call

theorem bit6 : lift (6#u64 &&& 1#u64)=ok 0#u64 := rfl
theorem bit13 : lift (13#u64 &&& 1#u64)=ok 1#u64 := rfl

theorem carry_tail : bounded_append_carry_loop 6#u64 1#usize=ok 1#usize := by
  rw [bounded_append_carry_loop]
  simp only [if_pos (by scalar_tac : 1#usize<20#usize),bit6,bind_tc_ok,
    if_pos (by rfl : 0#u64=0#u64),ite_true,ite_false]

theorem carry : bounded_append_carry 13#u64=ok 1#usize := by
  unfold bounded_append_carry
  rw [bounded_append_carry_loop]
  simp only [if_pos (by scalar_tac : 0#usize<20#usize),bit13,bind_tc_ok,
    if_neg (by scalar_tac : ¬(1#u64=0#u64)),shift,
    JFr_IndexArithmetic.add 0#usize 1#usize rfl,carry_tail,ite_true,ite_false]

#print axioms capacity
#print axioms shift
#print axioms bit6
#print axioms bit13
#print axioms carry_tail
#print axioms carry
end AspisR1.JFu_TransitionArithmetic
end
