import NFC_FirstJoin
import NFC_LaterJoin
set_option autoImplicit false
noncomputable section
namespace AspisR1.NFC_TailAssociation
open Aeneas Aeneas.Std Result NEV_DotCarrier NFC_TailSources
/-- Full Result join uses the separately checked first/later cuts. -/
theorem source (q : Array U8 608#usize) (g : NEV_DotInputs.Coefficients) (slot : Usize) :
    NFA_SuffixFactor.tail q g slot=body q g slot := by
  unfold body
  simp only [NFC_FirstJoin.association,NFC_LaterJoin.association]
  simp only [NFA_SuffixFactor.tail,NFA_TailQM.read,Aeneas.Std.uncurry,
    bind_assoc_eq,bind_tc_ok]
#print axioms source
end AspisR1.NFC_TailAssociation
end
