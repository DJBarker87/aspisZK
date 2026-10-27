import FIz_DigestPrefix
import FIz_DigestFold
import FIz_DigestSuffix
import FIy_PublicDigest
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIz_PublicDigest
attribute [local irreducible] List.foldl R0P.digestAddBinding
open FIv_NativeValue (K)
open FIw_PublicModel (Public Openings Selectors)
theorem value (p : Public) (o : Openings) (s : Selectors) :
    FIy_PublicDigest.model p o s=R0P.publicDigestLanes
      (FIw_PublicModel.ofPublic p) (FIw_PublicModel.openings o) (FIw_PublicModel.selector s) := by
  unfold FIy_PublicDigest.model
  rw [FIz_DigestSuffix.value,FIz_DigestFold.value p o s 20 0 (by decide),FIz_DigestPrefix.value]
  unfold R0P.publicDigestLanes R0P.digestKeys
  have indices : (List.ofFn (fun i : Fin 20=>R0P.DigestKey.frontier ⟨0+i.val,by omega⟩))=
      List.ofFn R0P.DigestKey.frontier := by rfl
  rw [indices]
  simp only [FIz_DigestPrefix.keys,FIz_DigestSuffix.keys,List.foldl_append]
  congr 1
#print axioms value
end AspisR1.FIz_PublicDigest
end
