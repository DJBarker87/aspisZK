import RPu_FIz_DigestBinding
import RPu_FIy_PublicDigestPrefix
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIz_DigestPrefix
open FIv_NativeValue (K)
open FIw_PublicModel (Public Openings Selectors)
def keys (p : R0P.Public K) : List R0P.DigestKey :=
  [.anchor,.nullifier]++(match p.recipient with | none=>[] | some _=>[.recipient])++[.change]
theorem value (p : Public) (o : Openings) (s : Selectors) :
    FIy_PublicDigestPrefix.model p o s=
      (keys (FIw_PublicModel.ofPublic p)).foldl (fun acc key=>R0P.digestAddBinding acc
        (FIw_PublicModel.selector s (R0P.digestRow (FIw_PublicModel.ofPublic p) key))
        (FIw_PublicModel.openings o).z (R0P.digestStart (FIw_PublicModel.ofPublic p) key)
        (R0P.digestTarget (FIw_PublicModel.ofPublic p) key)) (fun _=>0) := by
  unfold FIy_PublicDigestPrefix.model
  dsimp only
  rw [FIz_DigestBinding.value s o.z ⟨907,by decide⟩,FIz_DigestBinding.value s o.z ⟨427,by decide⟩]
  cases hr : p.recipient with
  | none=>
    simp only [hr]
    rw [FIz_DigestBinding.value s o.z ⟨523,by decide⟩]
    simp only [keys,FIw_PublicModel.ofPublic,hr,Option.map_none,List.nil_append,List.cons_append,
      List.foldl_cons,List.foldl_nil,R0P.digestRow,R0P.digestStart,R0P.digestTarget]
    rfl
  | some d=>
    simp only [hr]
    rw [FIz_DigestBinding.value s o.z ⟨475,by decide⟩,FIz_DigestBinding.value s o.z ⟨523,by decide⟩]
    simp only [keys,FIw_PublicModel.ofPublic,hr,Option.map_some,List.nil_append,List.cons_append,
      List.foldl_cons,List.foldl_nil,R0P.digestRow,R0P.digestStart,R0P.digestTarget]
    rfl
#print axioms value
end AspisR1.FIz_DigestPrefix
end
