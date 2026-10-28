import NBS_GeometryDomains
set_option autoImplicit false
noncomputable section
namespace NCB_PrefixNativeStep
open Aeneas Aeneas.Std Result ControlFlow AspisR1
open AspisR1.Port4C_NativePrefix S7Kani2PrefixLoop
/-- Three local native cuts compose at ONE arbitrary prefix prestate.
The read, append frame and modular reply are tied to the same flat/index/product.
Ownership and the native whole-loop trace are not assumed or concluded. -/
theorem source (ops : Leaves)
    (multiply : ops.mul=AspisR1Qm31ArithmeticProbe.field.M31.mul)
    (flat : Slice U32) (prefixes after : alloc.vec.Vec U32)
    (product productAfter : U32) (index : Usize)
    (size : flat.val.length≤110) (active : index.val<flat.val.length)
    (capacity : prefixes.val.length≤110)
    (nativePush : after.val=prefixes.val++[product])
    (nativeMul : productAfter.val=(product.val*(flat.val[index.val]'active).val)%2147483647) :
    ∃ next : Usize, next.val=index.val+1 ∧
      verifier.batch_prefix_products_loop.body ops flat prefixes product index=
        ok (cont (after,productAfter,next)) := by
  obtain ⟨x,read,word⟩ := WP.spec_imp_exists (Slice.index_usize_spec flat index active)
  obtain ⟨next,push,contents⟩ := WP.spec_imp_exists
    (alloc.vec.Vec.push_spec prefixes product (by
      have h : 110<Usize.max := by scalar_tac
      omega))
  have same : next=after := Subtype.ext (contents.trans nativePush.symm)
  subst next
  have value : wordMul product x=productAfter := by
    apply UScalar.eq_of_val_eq
    change (product.val*x.val)%2147483647=productAfter.val
    change x=flat.val[index.val] at word
    rw [word]
    exact nativeMul.symm
  let next := Usize.wrapping_add index 1#usize
  refine ⟨next,Port3_Wrapping.increment index (by omega),?_⟩
  have running : index<Slice.len flat := active
  simp only [verifier.batch_prefix_products_loop.body,if_pos running,read,push,
    multiply,multiply_word,value,lift,bind_tc_ok]
  rfl

theorem stopped (ops : Leaves) (flat : Slice U32) (prefixes : alloc.vec.Vec U32)
    (product : U32) (index : Usize) (stop : flat.val.length ≤ index.val) :
    verifier.batch_prefix_products_loop.body ops flat prefixes product index=
      ok (done (prefixes,product)) := by
  have inactive : ¬index<Slice.len flat := by change ¬index.val<flat.val.length;omega
  simp only [verifier.batch_prefix_products_loop.body,if_neg inactive]
#print axioms source
#print axioms stopped
end NCB_PrefixNativeStep
end
