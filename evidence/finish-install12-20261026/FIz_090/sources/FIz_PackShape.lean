import FIx_PreweightedPack
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIz_PackShape
open Aeneas Aeneas.Std
open FIv_NativeValue (K)
open ExtractedMaskQmPackBase4Arithmetic (iBasis uBasis)
theorem value (a : Fin 4 → K) : FIx_PreweightedPack.pack a=
    a 0+iBasis*a 1+uBasis*a 2+(iBasis*uBasis)*a 3 := by
  have z0 : (⟨0,by decide⟩ : Fin (4#usize).val)=(0 : Fin 4) := by apply Fin.ext;rfl
  have z1 : (⟨1,by decide⟩ : Fin (4#usize).val)=(1 : Fin 4) := by apply Fin.ext;rfl
  have z2 : (⟨2,by decide⟩ : Fin (4#usize).val)=(2 : Fin 4) := by apply Fin.ext;rfl
  have z3 : (⟨3,by decide⟩ : Fin (4#usize).val)=(3 : Fin 4) := by apply Fin.ext;rfl
  unfold FIx_PreweightedPack.pack
  rw [z0,z1,z2,z3]
#print axioms value
end AspisR1.FIz_PackShape
end
