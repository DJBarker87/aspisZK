import NDO_JFy_BoundedCanonical
import NDO_JGj_RawBounds
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGj_BoundedRawBuilder
open Aeneas Aeneas.Std Result FIq_Native
theorem source {C : Type} (f : core.ops.function.FnMut C Usize U64) (c : C) (b : Nat)
    (step : ∀ i : Usize,i.val<(4#usize).val → ∃ x,f.call_mut c i=ok (x,c) ∧ x.val<b) :
    ∃ out,array_from_fn_copy 4#usize core.marker.CopyU64 f 0#u64 c=ok out ∧ JGj_RawBounds.Bound out b := by
  obtain ⟨out,ro,bo⟩ := JFy_BoundedCanonical.source (fun x : U64=>x.val<b) 4#usize f c step
  refine ⟨out,ro,?_⟩
  intro j
  exact bo _ (List.getElem_mem _)
#print axioms source
end AspisR1.JGj_BoundedRawBuilder
end
