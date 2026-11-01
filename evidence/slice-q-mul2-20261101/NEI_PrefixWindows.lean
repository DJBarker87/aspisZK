import NEI_PrefixStep
import KMX_CopyMeaning
set_option autoImplicit false
noncomputable section
namespace NEI_PrefixWindows
open Aeneas Aeneas.Std Result ControlFlow AspisR1

/-- One arbitrary value window plus the length determines the entire append. -/
theorem append_from_windows {T : Type} (before after : List T) (value : T)
    (length : after.length = before.length + 1)
    (windows : ∀ (offset : Nat) (valid : offset < after.length),
      after[offset] = if h : offset < before.length then before[offset] else value) :
    after = before ++ [value] := by
  apply List.ext_getElem
  · simp only [List.length_append,List.length_singleton]
    exact length
  · intro offset ha hb
    rw [windows offset ha]
    by_cases inside : offset < before.length
    · simp only [dif_pos inside,List.getElem_append_left inside]
    · have atEnd : offset = before.length := by omega
      subst offset
      simp

/-- Exact KMX successful-shrink law on an arbitrary surviving location. -/
theorem surviving_copy {T : Type} (src dst : Nat → T) (oldSize newSize offset : Nat)
    (shrinking : newSize ≤ oldSize) (inside : offset < newSize) :
    KMX_CopyMeaning.loop src dst 0 (min oldSize newSize) offset = src offset := by
  rw [KMX_CopyMeaning.realloc_prefix]
  simp only [Nat.min_eq_right shrinking,if_pos inside]

/-- The field operation's actual reply is admitted by the multiplication-free
oracle. The source law supplies its exact value; Kani assumes only the bound. -/
theorem specialize_field_reply (lhs rhs : U32) (P : U32 → Prop)
    (universal : ∀ reply, reply.val < 2147483647 → P reply) :
    ∃ reply, NEG_PrefixFull.aspis_core.field.M31.mul lhs rhs = ok reply ∧
      reply.val = (lhs.val * rhs.val) % 2147483647 ∧ P reply := by
  obtain ⟨reply,run,value,canonical⟩ := NEG_PrefixStep.multiply lhs rhs
  exact ⟨reply,run,value,universal reply canonical⟩

/-- The native local window facts specialize to the SAME emitted source step.
Only primitive append and field-reply observations enter the premises. -/
theorem source_step (flat : Slice U32) (before after : alloc.vec.Vec U32)
    (product reply : U32) (index : Usize) (size : flat.val.length ≤ 110)
    (running : index.val < flat.val.length) (length : before.val.length = index.val)
    (afterLength : after.val.length = before.val.length + 1)
    (windows : ∀ (offset : Nat) (valid : offset < after.val.length),
      after.val[offset] = if h : offset < before.val.length then before.val[offset] else product)
    (fieldReply : reply.val = (product.val * (flat.val[index.val]'running).val) % 2147483647) :
    ∃ next : Usize, next.val = index.val + 1 ∧
      NEG_PrefixFull.batch_prefix_products_loop.body flat before product index =
        ok (cont (after,reply,next)) := by
  have pushed : after.val = before.val ++ [product] :=
    append_from_windows before.val after.val product afterLength windows
  obtain ⟨next,nextValue,body⟩ := NCB_PrefixNativeStep.source NEG_PrefixAssociation.ops rfl
    flat before after product reply index size running (by omega) pushed fieldReply
  exact ⟨next,nextValue,(NEG_PrefixAssociation.step flat before product index).trans body⟩

#print axioms append_from_windows
#print axioms surviving_copy
#print axioms specialize_field_reply
#print axioms source_step
end NEI_PrefixWindows
end
