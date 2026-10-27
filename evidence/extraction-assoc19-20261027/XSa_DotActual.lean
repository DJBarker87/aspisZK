import XSa_DotModel
open Aeneas Aeneas.Std Result
open XRo_Join_Carriers XSa_DotCarriers
set_option autoImplicit false
namespace XSa_DotActual

theorem push (self : Dot) (a b : E.Q)
 (ha : XSa_QRawTotal.canonical a) (hb : XSa_QRawTotal.canonical b) :
 ∃ out : Dot, _root_.fast_pairing.canonical.Dot.push self (XRn_Join_toQ a) (XRn_Join_toQ b)=ok out ∧
 AspisR1EbyKPushDotBackend.dotViaRaw AspisR1EbyKPushDecodedProductUpdate.QRaw
   ⟨self.sums⟩ (XRn_Join_toQ a) (XRn_Join_toQ b)=ok ⟨out.sums⟩ := by
 obtain ⟨raw,call,words⟩ := XSa_RawActual.actual a b ha hb
 refine ⟨⟨AspisR1DotPushLocal.Proof.updatedSums self.sums raw⟩,
   XSa_DotModel.model self _ _ raw words,?_⟩
 unfold AspisR1EbyKPushDotBackend.dotViaRaw
 rw [AspisR1DotPushLocal.Proof.push_total_from_raw _ _ _ _ raw call,bind_tc_ok]

#print axioms push
end XSa_DotActual
