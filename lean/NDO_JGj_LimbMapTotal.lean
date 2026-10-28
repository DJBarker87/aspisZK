import NDO_JGa_Map
import RPv_FJb_LimbMap
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGj_LimbMapTotal
open Aeneas Aeneas.Std Result FIq_Native
open FIv_NativeArithmetic (NQ)
theorem source {N : Usize} (input : Array NQ N) :
    ∃ out,FIq_Native.core.array.Array.map (BuiltinFnMut NQ (Array U32 4#usize))
      input state_only_poseidon.extension_limbs=ok out := by
  obtain ⟨out,ho,_⟩ := JGa_Map.source (BuiltinFnMut NQ (Array U32 4#usize))
    (fun _=>True) input state_only_poseidon.extension_limbs
    (by intro x hx;exact ⟨FJb_LimbMap.words x,rfl,True.intro⟩)
  exact ⟨out,ho⟩
#print axioms source
end AspisR1.JGj_LimbMapTotal
end
