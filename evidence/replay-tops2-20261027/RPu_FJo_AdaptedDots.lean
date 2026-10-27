import RPu_FJo_FourLiteral
import RPu_FJi_ArrayAdapter
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJo_AdaptedDots
open Aeneas Aeneas.Std Result MultiproofConeCanonical
/-- The installed adapter's four values on its actual opening and powers. -/
theorem value (opening : Slice U8) (g : Array FIp_DotsAdapter.E 29#usize)
    (out : Array FIp_DotsAdapter.E 4#usize) (gamma : AspisWideTower.WideExact)
    (hg : FIo_ArrayCanon.Holds (FIp_DotsAdapter.toArray g))
    (powers : ∀ l : Fin 29,FIp_ArrayValue.value (FIp_DotsAdapter.toArray g) l.val=gamma^l.val)
    (c1 : MixedLeafEncoding.C1) (c2 : MixedLeafEncoding.C2)
    (d1 : MixedLeafDecoder.decodeC1 ((bytesOf opening.val).take 480)=some c1)
    (d2 : MixedLeafDecoder.decodeC2 (((bytesOf opening.val).drop 480).take 128)=some c2)
    (run : FIp_DotsAdapter.dots opening g=ok out) :
    ∀ s : Fin 4,Port5Q1_OpeningValues.values out s=FJo_FourLiteral.formula gamma c1 c2 s := by
  obtain ⟨native,called,same⟩ := FIp_DotsAdapter.reached opening g out run
  rw [←same]
  intro s
  rw [FJi_ArrayAdapter.values]
  exact FJo_FourLiteral.value opening _ native gamma hg powers c1 c2 d1 d2 called s
#print axioms value
end AspisR1.FJo_AdaptedDots
end
