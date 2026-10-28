import NDH_RegistryReference.Funs
import NDH_PolicySlot
set_option autoImplicit false
namespace NDH_RegistryBinding
open Aeneas Aeneas.Std Result

theorem reference (value : Array U8 32#usize) :
    NDH_RegistryReference.binding_ref value =
      core.array.equality.PartialEqArray.eq core.cmp.PartialEqU8
        value (Array.repeat 32#usize 0#u8) := rfl

/-- Natural byte-value law for the zero-binding carrier; this is independent
of allocator/decoder/native-call association, which remains explicit. -/
theorem all_zero (xs : List U8) :
    (∀ x ∈ xs, x=0#u8) ↔ xs=List.replicate xs.length 0#u8 := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.mem_cons,forall_eq_or_imp,List.length_cons,List.replicate_succ,List.cons.injEq]
    exact and_congr Iff.rfl ih

#print axioms reference
#print axioms all_zero
end NDH_RegistryBinding
