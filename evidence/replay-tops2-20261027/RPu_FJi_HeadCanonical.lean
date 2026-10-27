import RPu_JFv_TX2_ScalarMeaning
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJi_HeadCanonical
open Aeneas Aeneas.Std Result

theorem value (limbs : Array U64 8#usize) (head : FIo_Install.NE)
    (run : JFs_TX2_DotSuffix.scalarFinish limbs=ok head) : FIo_WideValues.Canon head := by
  obtain ⟨out,hr,hc,_⟩ := JFv_TX2_ScalarMeaning.source limbs
  have same := Result.ok.inj (hr.symm.trans run)
  exact same ▸ hc
#print axioms value
end AspisR1.FJi_HeadCanonical
end
