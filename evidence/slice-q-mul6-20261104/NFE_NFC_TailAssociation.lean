import NFE_NFC_FirstJoin
import NFE_NFC_LaterJoin
set_option autoImplicit false
noncomputable section
namespace AspisR1.NFE_NFC_TailAssociation
open Aeneas Aeneas.Std Result NEV_DotCarrier NFE_NFC_TailSources
/-- Full Result join uses the separately checked first/later cuts. -/
theorem source (q : Array U8 608#usize) (g : NEV_DotInputs.Coefficients) (slot : Usize) :
    NFE_NFA_SuffixFactor.tail q g slot=body q g slot := by
  have right {T : Type} (r : Result T) : (do let x ← r; ok x)=r := by cases r <;> rfl
  unfold body
  simp only [NFE_NFC_FirstJoin.association,NFE_NFC_LaterJoin.association]
  simp only [NFE_NFA_SuffixFactor.tail,NFA_TailQM.read,Aeneas.Std.uncurry,
    bind_assoc_eq,bind_tc_ok,right]
#print axioms source
end AspisR1.NFE_NFC_TailAssociation
end
