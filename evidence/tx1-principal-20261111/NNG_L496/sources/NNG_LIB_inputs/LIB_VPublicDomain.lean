import LIB_VCarriers
set_option autoImplicit false
noncomputable section
namespace LIB_VPublicDomain
open Aeneas Aeneas.Std LIB_VCarriers
open AspisR1
def publicDigestDom (p : Public) : Prop :=
 NKR_DigestChildren.Domain (NKR_TermPublic.value (FIq_Carriers.toPublic p))
def publicAssetDom (p : Public) : Prop :=
 (NKR_TermPublic.value (FIq_Carriers.toPublic p)).asset_id.val<2147483647
/-- The public-only conjunction of BOTH recorded TX1:256 own-input clauses. -/
def publicDom (p : Public) : Prop := publicDigestDom p ∧ publicAssetDom p
def withAsset : Public → U32 → Public
 | .Transfer pay tr,a => .Transfer {pay with asset_id:=a} tr
 | .Withdrawal pay tr,a => .Withdrawal {pay with asset_id:=a} tr
theorem digest_withAsset (p : Public) (a : U32) :
 publicDigestDom (withAsset p a) ↔ publicDigestDom p := by
 cases p <;> constructor <;> intro h <;>
  exact ⟨h.anchor,h.nullifier,h.recipient,h.change,h.frontier,h.nextRoot,h.nextFrontier⟩
theorem asset_withAsset (p : Public) (a : U32) :
 (NKR_TermPublic.value (FIq_Carriers.toPublic (withAsset p a))).asset_id = a := by cases p <;> rfl
/-- LIB0_MAP's hd-only shorthand does not imply the separately recorded asset
clause. This is a field-map finding, not a frozen-spec or source modification. -/
theorem hd_omits_asset (p : Public) (h : publicDigestDom p) :
 publicDigestDom (withAsset p 2147483647#u32) ∧
 ¬ publicAssetDom (withAsset p 2147483647#u32) := by
 refine ⟨(digest_withAsset p _).mpr h,?_⟩
 unfold publicAssetDom
 rw [asset_withAsset]
 change ¬2147483647<2147483647
 omega
#print axioms digest_withAsset
#print axioms asset_withAsset
#print axioms hd_omits_asset
end LIB_VPublicDomain
