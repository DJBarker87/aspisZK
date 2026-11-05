import NGW_FactorWrite
import RPz7_FIo_Install
set_option autoImplicit false
namespace NGW_BoxModel
open Aeneas Aeneas.Std Result NGW_ConstructorQM NGW_FactorWrite

theorem source (variant : FIn_WeightsExtract.FInVariant) (factors : Factors)
 (points : Array (Array Q 10#usize) 3#usize) (extra : Array Q 2#usize) :
 FIn_WeightsExtract.Weights.box_from_parts variant factors points extra=
 ok (⟨variant,factors,points,extra⟩ : FIn_WeightsExtract.Weights) := rfl

theorem native_shape (variant : FIn_WeightsExtract.FInVariant) (factors : Factors)
 (points : Array (Array Q 10#usize) 3#usize) (extra : Array Q 2#usize) :
 AspisR1.FIo_Install.toWeights (⟨variant,factors,points,extra⟩ : FIn_WeightsExtract.Weights)=
 (⟨AspisR1.FIo_Install.variant variant,
   AspisR1.FIn_WeightsInstall.mapArray (AspisR1.FIn_WeightsInstall.mapArray (AspisR1.FIn_WeightsInstall.mapArray AspisR1.FIo_Install.toQ)) factors,
   AspisR1.FIn_WeightsInstall.mapArray (AspisR1.FIn_WeightsInstall.mapArray AspisR1.FIo_Install.toQ) points,
   AspisR1.FIn_WeightsInstall.mapArray AspisR1.FIo_Install.toQ extra⟩ : FIo_Native.weights.Weights) := rfl

#print axioms native_shape

#print axioms source
end NGW_BoxModel
