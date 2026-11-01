import NEG_PrefixAssociation
import ExtractedCurrentReducer
set_option autoImplicit false
noncomputable section
namespace NEG_PrefixStep
open Aeneas Aeneas.Std Result AspisR1
/-- No canonical-input precondition is needed by this actual emitted M31 call. -/
theorem multiply (a b : U32) :
    ∃ z : U32, NEG_PrefixFull.aspis_core.field.M31.mul a b = ok z ∧
      z.val = (a.val*b.val)%2147483647 ∧ z.val<2147483647 := by
  exact ExtractedCurrentReducer.current_mul_mod a b
#print axioms multiply
theorem append (v : alloc.vec.Vec U32) (x : U32) (len : v.val.length<110) :
    ∃ w, alloc.vec.Vec.push v x = ok w ∧ w.val = v.val ++ [x] := by
  have fit : v.val.length+1 ≤ U32.max := by scalar_tac
  unfold alloc.vec.Vec.push
  simp only [fit,decide_true,Bool.true_or, ↓reduceDIte]
  refine ⟨_,rfl,?_⟩
  exact List.concat_eq_append v.val x

/-- One entire emitted prefix iteration, all stored U32 inputs admitted.
The index/length invariant is explicit and no output success is a premise. -/
theorem step (flat : Slice U32) (prefixes : alloc.vec.Vec U32)
    (product : U32) (index : Usize) (active : index < Slice.len flat)
    (size : flat.val.length≤110) (length : prefixes.val.length=index.val) :
    ∃ ps z, NEG_PrefixFull.batch_prefix_products_loop.body flat prefixes product index =
      ok (ControlFlow.cont (ps,z,UScalar.wrapping_add index 1#usize)) ∧
      ps.val=prefixes.val++[product] ∧ z.val<2147483647 := by
  have bound : index.val<flat.val.length := by scalar_tac
  obtain ⟨value,read,_⟩ := WP.spec_imp_exists (Slice.index_usize_spec flat index bound)
  obtain ⟨ps,push,pval⟩ := append prefixes product (by omega)
  obtain ⟨z,mul,_,canonical⟩ := multiply product value
  refine ⟨ps,z,?_,pval,canonical⟩
  unfold NEG_PrefixFull.batch_prefix_products_loop.body
  simp only [active,if_true,read,push,mul,
    NEG_PrefixAssociation.guarded_increment index (Slice.len flat) active,bind_tc_ok]
#print axioms append
#print axioms step
end NEG_PrefixStep
end
