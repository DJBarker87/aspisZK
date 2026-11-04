import NEI_PrefixWindows
import NEI_PrefixProduct
set_option autoImplicit false
noncomputable section
namespace NET_PrefixClosure
open Aeneas Aeneas.Std Result ControlFlow AspisR1

/-- Current caller lengths select one of the native capacity classes. -/
theorem capacity_class (count index : Nat) (bound : count ≤ 22)
    (active : index < count * 5) :
    1 ≤ count ∧ count ≤ 22 ∧ index < count * 5 ∧ count * 5 ≤ 110 := by omega

/-- The initialized prefix invariant preserves the nongrowing allocation
condition after an arbitrary active native step. No spare word is assumed. -/
theorem allocation_invariant (count index : Nat) (bound : count ≤ 22)
    (active : index < count * 5) :
    index + 1 ≤ count * 5 ∧ index + 1 ≤ 110 ∧
    (index + 1 < count * 5 → index + 1 < 110) := by omega

/-- Reuse the peer's source-step assembly, with the concrete native capacity
invariant and complete arbitrary-index frame observations. -/
theorem step (flat : Slice U32) (before after : alloc.vec.Vec U32)
    (product reply : U32) (index : Usize) (count : Nat)
    (bound : count ≤ 22) (flatLength : flat.val.length = count * 5)
    (active : index.val < flat.val.length) (length : before.val.length = index.val)
    (afterLength : after.val.length = before.val.length + 1)
    (windows : ∀ (offset : Nat) (valid : offset < after.val.length),
      after.val[offset] = if h : offset < before.val.length then before.val[offset] else product)
    (fieldReply : reply.val = (product.val * (flat.val[index.val]'active).val) % 2147483647) :
    ∃ next : Usize, next.val = index.val + 1 ∧
      NEG_PrefixFull.batch_prefix_products_loop.body flat before product index =
        ok (cont (after,reply,next)) := by
  exact NEI_PrefixWindows.source_step flat before after product reply index
    (by omega) active length afterLength windows fieldReply

/-- Whole emitted result and the installed finite-list model agree. The
native one-step association and its physical interpretation remain separately
checked certificate components; this theorem does not assume a native result. -/
theorem complete (flat : Slice U32) (count : Nat)
    (bound : count ≤ 22) (flatLength : flat.val.length = count * 5) :
    ∃ prefixes product,
      NEG_PrefixFull.batch_prefix_products flat = ok (prefixes,product) ∧
      (prefixes.val,product) = S7Kani2PrefixLoop.model flat.val [] 1#u32 := by
  exact NEI_PrefixStep.total flat (by omega)

/-- Primitive observations are ordered in one trace with one evolving Vec.
No whole-loop output premise is used. This is the reused finite-induction
consumer for the native window observations, rather than a second model. -/
theorem observed_result (flat : Slice U32) (count : Nat)
    (bound : count ≤ 22) (flatLength : flat.val.length = count * 5)
    (final : alloc.vec.Vec U32) (product : U32)
    (cuts : NCB_PrefixCutTrace.Cuts flat 0#usize (alloc.vec.Vec.new U32) 1#u32 final product) :
    NEG_PrefixFull.batch_prefix_products flat = ok (final,product) ∧
      (final.val,product) = S7Kani2PrefixLoop.model flat.val [] 1#u32 := by
  have size : flat.val.length ≤ 110 := by omega
  have run := NCB_PrefixCutTrace.associated NEG_PrefixAssociation.ops rfl
    flat size 0#usize (alloc.vec.Vec.new U32) final 1#u32 product cuts rfl
  have entry : Port4C_NativePrefix.verifier.batch_prefix_products NEG_PrefixAssociation.ops flat =
      ok (final,product) := by
    simp only [Port4C_NativePrefix.verifier.batch_prefix_products,
      NEG_PrefixAssociation.ops,bind_tc_ok,alloc.vec.Vec.with_capacity]
    exact run
  exact ⟨(NEG_PrefixAssociation.source flat).trans entry,
    NCB_PrefixCutTrace.meaning NEG_PrefixAssociation.ops rfl rfl flat size final product cuts⟩

#print axioms NEI_PrefixProduct.actual
#print axioms capacity_class
#print axioms allocation_invariant
#print axioms step
#print axioms complete
#print axioms observed_result
end NET_PrefixClosure
end
