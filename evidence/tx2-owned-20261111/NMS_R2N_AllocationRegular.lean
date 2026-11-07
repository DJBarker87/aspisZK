import NMS_R2N_Regular
set_option autoImplicit false
namespace NMS_R2N_AllocationRegular
open Aeneas Aeneas.Std
/-- Allocation can stop, but a returning arm cannot change the continuation's
value. This avoids normalizing a known-ok Result binder in large folds. -/
theorem bind {A : Type} (meaning : RSL.Spec A) (code : Result A)
 (regular : NMS_R2N_Regular.Law meaning code) :
 NMS_R2N_Regular.Law (RSL.Spec.bind RSL.Spec.alloc (fun _ => meaning)) code := by
 intro env value events run
 obtain ⟨_,_,suffix,_,last,_⟩ := NMS_R2Success.bind_return _ _ _ _ _ run
 exact regular env value suffix last
#print axioms bind
end NMS_R2N_AllocationRegular
