import Port4C_NativePrefix

set_option autoImplicit false
noncomputable section
namespace AspisR1.Port4C_PrefixMeaning
open Aeneas Aeneas.Std Result ControlFlow AspisR1Stage2
open Port4C_NativePrefix
open S7Kani2PrefixLoop (wordMul model multiply_word)

theorem loop_total (ops : Leaves)
    (multiply : ops.mul=AspisR1Qm31ArithmeticProbe.field.M31.mul)
    (flat : Slice U32) (prefixes : alloc.vec.Vec U32) (product : U32)
    (index : Usize) (fuel : Nat) (bound : flat.val.length≤110)
    (remaining : index.val+fuel=flat.val.length) (capacity : prefixes.val.length+fuel≤110) :
    ∃ out finalProduct,
      verifier.batch_prefix_products_loop ops flat prefixes product index=ok (out,finalProduct) ∧
      (out.val,finalProduct)=model (flat.val.drop index.val) prefixes.val product := by
  induction fuel generalizing prefixes product index with
  | zero =>
    have inactive : ¬index<Slice.len flat := by change ¬index.val<flat.val.length; omega
    refine ⟨prefixes,product,?_,?_⟩
    · unfold verifier.batch_prefix_products_loop
      rw [Aeneas.Std.loop.eq_def]
      simp only [Aeneas.Std.uncurry,verifier.batch_prefix_products_loop.body,if_neg inactive]
    · have empty : flat.val.drop index.val=[] := List.drop_eq_nil_iff.mpr (by omega)
      rw [empty,model]
  | succ fuel ih =>
    have active : index<Slice.len flat := by change index.val<flat.val.length; omega
    have hcap : prefixes.val.length<Usize.max := by
      have cap : 110<Usize.max := by scalar_tac
      omega
    obtain ⟨x,hread,hx⟩ := WP.spec_imp_exists (Slice.index_usize_spec flat index (by change index.val<flat.val.length; omega))
    change x=flat.val[index.val] at hx
    obtain ⟨prefixes1,hpush,hprefix⟩ := WP.spec_imp_exists (alloc.vec.Vec.push_spec prefixes product hcap)
    let index1 := Usize.wrapping_add index 1#usize
    have hv : index1.val=index.val+1 := Port3_Wrapping.increment index (by omega)
    have cap1 : prefixes1.val.length+fuel≤110 := by rw [hprefix,List.length_append,List.length_singleton]; omega
    obtain ⟨out,finalProduct,tail,meaning⟩ := ih prefixes1 (wordMul product x) index1 (by omega) cap1
    have bodyRun : verifier.batch_prefix_products_loop.body ops flat prefixes product index=
        ok (cont (prefixes1,wordMul product x,index1)) := by
      simp only [verifier.batch_prefix_products_loop.body,if_pos active,hread,hpush,
        multiply,multiply_word,lift,bind_tc_ok]
      rfl
    refine ⟨out,finalProduct,?_,?_⟩
    · unfold verifier.batch_prefix_products_loop
      rw [Aeneas.Std.loop.eq_def]
      simp only [Aeneas.Std.uncurry,bodyRun]
      exact tail
    · have hd : flat.val.drop index.val=x::flat.val.drop (index.val+1) := by
        simpa only [←hx] using (List.drop_eq_getElem_cons (l:=flat.val) (by change index.val<flat.val.length; omega))
      rw [hd,model]
      simpa only [hv,hprefix] using meaning

/-- Entire CURRENT prefix constructor, including empty allocation and ONE. -/
theorem total (ops : Leaves) (multiply : ops.mul=AspisR1Qm31ArithmeticProbe.field.M31.mul)
    (one : ops.one=ok (1#u32)) (flat : Slice U32) (bound : flat.val.length≤110) :
    ∃ out product,
      verifier.batch_prefix_products ops flat=ok (out,product) ∧
      (out.val,product)=model flat.val [] 1#u32 := by
  obtain ⟨out,product,run,meaning⟩ := loop_total ops multiply flat (alloc.vec.Vec.new U32)
    1#u32 0#usize flat.val.length bound (by simp) (by simpa using bound)
  refine ⟨out,product,?_,?_⟩
  · simp only [verifier.batch_prefix_products,one,bind_tc_ok,alloc.vec.Vec.with_capacity]
    exact run
  · simpa only [show (0#usize).val=0 from rfl,List.drop_zero,alloc.vec.Vec.new] using meaning

#print axioms loop_total
#print axioms total
end AspisR1.Port4C_PrefixMeaning
end
