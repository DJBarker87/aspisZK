import NEI_PrefixProduct
import NEG_ProductAbstraction
set_option autoImplicit false
noncomputable section
namespace NEV_PrefixAssembly
open Aeneas Aeneas.Std Result ControlFlow AspisR1

/-- Join separately observed append and old-word windows at the same prestate.
The native obligations are explicit; this is not a native append proof. -/
theorem windows (before after : alloc.vec.Vec U32) (product : U32)
    (length : after.val.length = before.val.length + 1)
    (appended : ∀ h : before.val.length < after.val.length,
      after.val[before.val.length] = product)
    (frame : ∀ (offset : Nat) (valid : offset < before.val.length),
      ∀ h : offset < after.val.length, after.val[offset] = before.val[offset]) :
    ∀ (offset : Nat) (valid : offset < after.val.length),
      after.val[offset] = if h : offset < before.val.length then before.val[offset] else product := by
  intro offset valid
  by_cases inside : offset < before.val.length
  · simp only [dif_pos inside]
    exact frame offset inside valid
  · simp only [dif_neg inside]
    have atEnd : offset = before.val.length := by omega
    subst offset
    exact appended valid

/-- No whole-buffer native premise: the three same-step primitive projections
combine with the imported actual multiplication law and finite-loop model. -/
theorem active (flat : Slice U32) (before after : alloc.vec.Vec U32)
    (product reply : U32) (index : Usize) (size : flat.val.length ≤ 110)
    (running : index.val < flat.val.length) (length : before.val.length = index.val)
    (afterLength : after.val.length = before.val.length + 1)
    (appended : ∀ h : before.val.length < after.val.length,
      after.val[before.val.length] = product)
    (frame : ∀ (offset : Nat) (valid : offset < before.val.length),
      ∀ h : offset < after.val.length, after.val[offset] = before.val[offset])
    (fieldReply : reply.val = (product.val * (flat.val[index.val]'running).val) % 2147483647) :
    ∃ next : Usize, next.val = index.val + 1 ∧
      NEG_PrefixFull.batch_prefix_products_loop.body flat before product index =
        ok (cont (after,reply,next)) := by
  exact NEI_PrefixWindows.source_step flat before after product reply index size running length
    afterLength (windows before after product afterLength appended frame) fieldReply

#print axioms windows
#print axioms active
#print axioms NEI_PrefixProduct.actual
#print axioms NEI_PrefixStep.total
end NEV_PrefixAssembly
end
