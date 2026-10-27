import FJb_ArrayTransport
import FIy_MapValue
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJb_LimbMap
open Aeneas Aeneas.Std Result FIq_Native
open FIv_NativeArithmetic (NQ)
def words (x : NQ) : Array U32 4#usize :=
  Array.make 4#usize [x.c0.a,x.c0.b,x.c1.a,x.c1.b]
/-- The ORIGINAL native builtin map returns exactly the ordered raw limbs. -/
theorem value {N : Usize} (a : Array NQ N) (out : Array (Array U32 4#usize) N)
    (run : FIq_Native.core.array.Array.map (BuiltinFnMut NQ (Array U32 4#usize))
      a state_only_poseidon.extension_limbs=ok out) :
    out=FJb_ArrayTransport.array words a := by
  unfold FIq_Native.core.array.Array.map at run
  have v := FIy_MapValue.value (BuiltinFnMut NQ (Array U32 4#usize))
    (fun _=>True) id words a state_only_poseidon.extension_limbs out (by
      intro x hx y last call
      change ok (words x,state_only_poseidon.extension_limbs)=ok (y,last) at call
      obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Result.ok.inj call)
      exact ⟨True.intro,rfl,rfl⟩) run
  apply Subtype.ext
  simpa only [List.map_id_fun,id] using v.2
#print axioms value
end AspisR1.FJb_LimbMap
end
