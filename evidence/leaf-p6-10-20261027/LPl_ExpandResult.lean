import LPl_ExpandOutput
open Aeneas Aeneas.Std Result LPl_Kit_Release
set_option autoImplicit false
namespace LPl.Expand

theorem double (bs : Slice U8) (bound : bs.val.length≤1856) :
    ∃ z : Usize, Slice.len bs * 2#usize = ok z ∧ z.val=2*bs.val.length := by
  obtain ⟨z,hz,hv⟩ := WP.spec_imp_exists (UScalar.mul_spec
    (x:=Slice.len bs) (y:=2#usize) (by scalar_tac))
  exact ⟨z,hz,by scalar_tac⟩

/-- Complete native owned output carrier on the aligned/length-matched source
    branch. Source guard gates separately cover every early Length error. -/
theorem native_result (bs before after : Slice U8)
    (bound : bs.val.length≤1856) (aligned : bs.val.length%16=0)
    (shape : before.val.length=2*bs.val.length)
    (trace : Trace bs.val before.val (bs.val.length/16) after.val) :
    compact.expand_values bs before = ok (.Ok (),after) := by
  have done : 32*(bs.val.length/16)=before.val.length := by omega
  have hafter := output bs.val before.val after.val _ trace done
  obtain ⟨z,mul,hz⟩ := double bs bound
  have z_eq : z=Slice.len before := by scalar_tac
  have values : LPl_A.Expand.loop bs.val before.val.length=after.val := hafter.symm
  rw [LPl_A.Expand.shipped_leaf_model]
  simp only [aligned,ne_eq,not_true_eq_false,Bool.false_eq_true,if_false,mul,bind_tc_ok,z_eq,
    bne_self_eq_false]
  rw [values]
  simp [bind_tc_ok,dif_pos after.property]

/-- Error preserves the SAME mutable output carrier on all bounded bad lengths. -/
theorem length_error (bs before : Slice U8)
    (bound : bs.val.length≤1856)
    (bad : bs.val.length%16≠0 ∨ before.val.length≠2*bs.val.length) :
    compact.expand_values bs before = ok (.Err .Length,before) := by
  rw [LPl_A.Expand.shipped_leaf_model]
  by_cases aligned : bs.val.length%16=0
  · have mismatch : before.val.length≠2*bs.val.length := by
      rcases bad with h|h
      · exact False.elim (h aligned)
      · exact h
    obtain ⟨z,mul,hz⟩ := double bs bound
    have neq : Slice.len before≠z := by scalar_tac
    simp only [aligned,ne_eq,not_true_eq_false,Bool.false_eq_true,if_false,mul,bind_tc_ok]
    simp [bind_tc_ok,Slice.len,hz,mismatch]
  · simp [aligned]

#print axioms double
#print axioms native_result
#print axioms length_error
end LPl.Expand
