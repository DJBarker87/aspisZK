import FIz_PackLinear
import R1ConcretePackBasis
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIz_ConcretePack
open FIv_NativeValue (K)
theorem value (a : Fin 4 → K) : FIx_PreweightedPack.pack a=R0P.pack4 ConcretePackBasis.basis a := by
  unfold FIx_PreweightedPack.pack R0P.pack4
  rfl
#print axioms value
end AspisR1.FIz_ConcretePack
end
