import NET_GeometryAllocation
import NFB_PhysicalFrame
set_option autoImplicit false
namespace NFB_ResizeTrace
open Aeneas.Std

/-- One native resize window reconstructs exactly one appended zero, retaining
all old values. Both observations concern the SAME before/after allocation. -/
theorem step (before after : List U32)
    (size : after.length=before.length+1)
    (old : ∀ j, j<before.length → after[j]?=before[j]?)
    (new : after[before.length]?=some 0#u32) : after=before++[0#u32] := by
 apply List.ext_getElem?
 intro j
 by_cases h : j<before.length
 · rw [old j h,List.getElem?_append_left h]
 · by_cases same : j=before.length
   · subst j
     rw [new,List.getElem?_append_right (by omega)]
     simp only [Nat.sub_self,List.getElem?_cons_zero]
   · rw [List.getElem?_eq_none (by omega : after.length≤j),
       List.getElem?_eq_none (by simp only [List.length_append,List.length_singleton]; omega)]

inductive Trace : Nat → List U32 → List U32 → Prop where
 | done (before : List U32) : Trace 0 before before
 | step (n : Nat) (before next final : List U32)
     (size : next.length=before.length+1)
     (old : ∀ j, j<before.length → next[j]?=before[j]?)
     (new : next[before.length]?=some 0#u32)
     (tail : Trace n next final) : Trace (n+1) before final

/-- Whole-buffer value law from one native iteration and an induction, without
unwinding a resize or assuming its whole output as a premise. -/
theorem complete {n : Nat} {before after : List U32} (trace : Trace n before after) :
    after=before++List.replicate n 0#u32 := by
 induction trace with
 | done => simp only [List.replicate_zero,List.append_nil]
 | step n before next final size old new tail ih =>
   rw [ih,step before next size old new,List.append_assoc]
   simp only [List.replicate_succ,List.singleton_append]

#print axioms step
#print axioms complete
end NFB_ResizeTrace
