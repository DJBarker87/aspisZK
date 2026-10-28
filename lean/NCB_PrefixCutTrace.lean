import NCB_PrefixNativeStep
set_option autoImplicit false
noncomputable section
namespace NCB_PrefixCutTrace
open Aeneas Aeneas.Std Result ControlFlow AspisR1
open AspisR1.Port4C_NativePrefix
/-- Ordered local observations of one actual buffer carrier. Each edge records
only the append frame and modular field reply, not a whole model loop result.
Existence for a frozen native execution remains a separate bridge obligation. -/
inductive Cuts (flat : Slice U32) : Usize → alloc.vec.Vec U32 → U32 →
    alloc.vec.Vec U32 → U32 → Prop
  | done (index : Usize) (buffer : alloc.vec.Vec U32) (product : U32)
      (stop : flat.val.length=index.val) : Cuts flat index buffer product buffer product
  | step (index : Usize) (buffer next final : alloc.vec.Vec U32) (product nextProduct finalProduct : U32)
      (active : index.val<flat.val.length)
      (pushed : next.val=buffer.val++[product])
      (multiplied : nextProduct.val=(product.val*(flat.val[index.val]'active).val)%2147483647)
      (tail : Cuts flat (Usize.wrapping_add index 1#usize) next nextProduct final finalProduct) :
      Cuts flat index buffer product final finalProduct

theorem associated (ops : Leaves)
    (multiply : ops.mul=AspisR1Qm31ArithmeticProbe.field.M31.mul)
    (flat : Slice U32) (size : flat.val.length≤110)
    (index : Usize) (buffer final : alloc.vec.Vec U32) (product finalProduct : U32)
    (cuts : Cuts flat index buffer product final finalProduct)
    (length : buffer.val.length=index.val) :
    verifier.batch_prefix_products_loop ops flat buffer product index=ok (final,finalProduct) := by
  induction cuts with
  | done index buffer product stop =>
    have body := NCB_PrefixNativeStep.stopped ops flat buffer product index (by omega)
    unfold verifier.batch_prefix_products_loop
    rw [Aeneas.Std.loop.eq_def]
    simp only [Aeneas.Std.uncurry,body]
  | step index buffer next final product nextProduct finalProduct active pushed multiplied tail ih =>
    have inc := Port3_Wrapping.increment index (by omega)
    have nextLen : next.val.length=(Usize.wrapping_add index 1#usize).val := by
      rw [pushed,List.length_append,List.length_singleton,length,inc]
    have tailRun := ih nextLen
    obtain ⟨cursor,cursorVal,body⟩ := NCB_PrefixNativeStep.source ops multiply flat buffer next
      product nextProduct index size active (by omega) pushed multiplied
    have cursorEq : cursor=Usize.wrapping_add index 1#usize := UScalar.eq_of_val_eq (cursorVal.trans inc.symm)
    rw [cursorEq] at body
    unfold verifier.batch_prefix_products_loop
    rw [Aeneas.Std.loop.eq_def]
    simp only [Aeneas.Std.uncurry,body]
    exact tailRun

/-- Reuse the existing complete buffer meaning theorem after associating the
ordered cuts. This adds no independently chosen native result or product. -/
theorem meaning (ops : Leaves)
    (multiply : ops.mul=AspisR1Qm31ArithmeticProbe.field.M31.mul)
    (one : ops.one=ok (1#u32)) (flat : Slice U32) (size : flat.val.length≤110)
    (final : alloc.vec.Vec U32) (finalProduct : U32)
    (cuts : Cuts flat 0#usize (alloc.vec.Vec.new U32) 1#u32 final finalProduct) :
    (final.val,finalProduct)=S7Kani2PrefixLoop.model flat.val [] 1#u32 := by
  have run := associated ops multiply flat size 0#usize (alloc.vec.Vec.new U32) final
    1#u32 finalProduct cuts rfl
  obtain ⟨out,product,source,value⟩ := Port4C_PrefixMeaning.total ops multiply one flat size
  have entry : verifier.batch_prefix_products ops flat=ok (final,finalProduct) := by
    simp only [verifier.batch_prefix_products,one,bind_tc_ok,alloc.vec.Vec.with_capacity]
    exact run
  have same := Prod.mk.inj (Result.ok.inj (source.symm.trans entry))
  rcases same with ⟨rfl,rfl⟩
  exact value
#print axioms associated
#print axioms meaning
end NCB_PrefixCutTrace
end
