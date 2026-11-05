import NHY_ZeroRun
import NHY_ZeroBinding
set_option autoImplicit false
noncomputable section
namespace NHY_AllZeroBridge
open Aeneas Aeneas.Std Result
attribute [local instance] Classical.propDecidable

-- Reuse of NDH_RegistryBinding.all_zero (namespace-only copy of its proof).
theorem list_zero (xs : List U8) :
    (∀ x ∈ xs, x=0#u8) ↔ xs=List.replicate xs.length 0#u8 := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.mem_cons,forall_eq_or_imp,List.length_cons,List.replicate_succ,List.cons.injEq]
    exact and_congr Iff.rfl ih

theorem view_zero (b : Slice U8) :
    NHY_ZeroRun.AllZero b 0 ↔ b.val=List.replicate b.val.length 0#u8 := by
  rw [←list_zero]
  constructor
  · intro all x member
    obtain ⟨i,hi,hx⟩ := List.mem_iff_getElem.mp member
    have hbyte := all i (Nat.zero_le i) hi
    simp only [NHY_ZeroStep.byte,List.getElem?_eq_getElem hi,Option.getD_some] at hbyte
    simpa only [hx] using hbyte
  · intro all i _ hi
    simp only [NHY_ZeroStep.byte,List.getElem?_eq_getElem hi,Option.getD_some]
    exact all _ (List.getElem_mem hi)

theorem array_zero (value : Array U8 32#usize) :
    NHY_ZeroRun.AllZero value.to_slice 0 ↔ value=Array.repeat 32#usize 0#u8 := by
  rw [view_zero]
  have size : value.val.length=32 := value.property
  change value.val=List.replicate value.val.length 0#u8 ↔ _
  rw [size]
  constructor
  · intro same
    have same' : value.val=(Array.repeat 32#usize 0#u8).val := same
    cases value
    cases same'
    rfl
  · intro same
    subst value
    rfl

theorem source (value : Array U8 32#usize) :
    NCX_Reference.required_binding_is_zero value = NHY_ZeroBinding.binding_ref value := by
  unfold NCX_Reference.required_binding_is_zero
  simp only [lift,bind_tc_ok]
  have cap : value.to_slice.val.length ≤ 768 := by
    change value.val.length ≤ 768
    have h := value.property
    change value.val.length=32 at h
    omega
  rw [NHY_ZeroRun.value _ cap,NHY_ZeroBinding.source]
  rw [propext (array_zero value)]

#print axioms list_zero
#print axioms view_zero
#print axioms array_zero
#print axioms source
end NHY_AllZeroBridge
