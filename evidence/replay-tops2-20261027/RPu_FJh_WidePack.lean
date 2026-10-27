import RPu_FIz_ConcretePack
import RPu_FJe_PackingLinear
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJh_WidePack
open FIv_NativeValue (K)
open ExtractedMaskQmPackBase4Arithmetic (iBasis uBasis)
/-- Explicit exact-field to Wide packing transport; no carrier identification. -/
theorem value (a : Fin 4 → K) :
    FIz_ConcretePack.embed (R0P.poseidonPackingFormula iBasis uBasis a)=
      R0P.pack4 ConcretePackBasis.basis (fun j=>FIz_ConcretePack.embed (a j)) := by
  have shape := FIz_PackShape.value a
  change FIx_PreweightedPack.pack a=R0P.poseidonPackingFormula iBasis uBasis a at shape
  exact (congrArg FIz_ConcretePack.embed shape).symm.trans (FIz_ConcretePack.value a)
#print axioms value
end AspisR1.FJh_WidePack
end
