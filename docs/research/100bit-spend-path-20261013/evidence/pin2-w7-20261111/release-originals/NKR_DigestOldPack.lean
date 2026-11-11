import NKR_DigestOldSource
import NKI_PackSum
import RPv_FIz_PublicDigest
set_option autoImplicit false
noncomputable section
namespace AspisR1.NKR_DigestOldPack
open Aeneas Aeneas.Std Result
open FIv_NativeValue (K)
open NKI_InitialPrefix (Public Openings Selectors)

def contribution (p : R0P.Public K) (o : R0P.Openings K) (s : R0P.Sel K)
 (key : R0P.DigestKey) (g : Fin 2) : K :=
 s (R0P.digestRow p key)*NJB_PackLinearity.pack (fun j=>
  o.z ⟨(R0P.digestStart p key).val+(NJX_DigestGroups.index g j).val,by have h:=(R0P.digestStart p key).isLt;have h':=(NJX_DigestGroups.index g j).isLt;omega⟩-
   R0P.digestTarget p key (NJX_DigestGroups.index g j))

/-- Packing the literal old source accumulator commutes with every ordered
finite call, including both optional guards and twenty frontier keys. -/
theorem fold (p : R0P.Public K) (o : R0P.Openings K) (s : R0P.Sel K) (g : Fin 2) :
 NJB_PackLinearity.pack (fun j=>R0P.publicDigestLanes p o s (NJX_DigestGroups.index g j))=
 ((R0P.digestKeys p).map (fun key=>contribution p o s key g)).sum := by
 have lanes : (fun j : Fin 4=>R0P.publicDigestLanes p o s (NJX_DigestGroups.index g j))=
  (fun j=>((R0P.digestKeys p).map (fun key=>s (R0P.digestRow p key)*
   (o.z ⟨(R0P.digestStart p key).val+(NJX_DigestGroups.index g j).val,by have h:=(R0P.digestStart p key).isLt;have h':=(NJX_DigestGroups.index g j).isLt;omega⟩-
     R0P.digestTarget p key (NJX_DigestGroups.index g j)))).sum) := by
  funext j
  unfold R0P.publicDigestLanes
  rw [R0P.digest_fold_eq]
  simp only [zero_add]
 rw [lanes,NKI_PackSum.source]
 apply congrArg List.sum
 apply List.map_congr_left
 intro key hk
 exact NJB_PackLinearity.scale _ _

/-- Whole emitted old body and exact packed call-key sum. This provides the
cohort endpoint without asserting equality to a newly invented model. -/
theorem source (p : Public) (o : Openings) (s : Selectors)
 (hp : NKR_DigestChildren.Domain p) (hz : FIw_ArrayValue.canonical o.z)
 (hh : FIw_ArrayValue.canonical s.high) (hl : FIw_ArrayValue.canonical s.low) :
 ∃ old,FIq_Native.pool_v1.pair_forest_semantic_terminal.public_digest_lanes p o s=ok old ∧
 FIw_ArrayValue.canonical old ∧ ∀ g,
 NJB_PackLinearity.pack (fun j=>FIw_ArrayValue.decoded old (NJX_DigestGroups.index g j))=
 ((R0P.digestKeys (FIw_PublicModel.ofPublic p)).map (fun key=>
  contribution (FIw_PublicModel.ofPublic p) (FIw_PublicModel.openings o) (FIw_PublicModel.selector s) key g)).sum := by
 obtain ⟨old,call,hc,values⟩ := NKR_DigestOldSource.source p o s hp hz hh hl
 refine ⟨old,call,hc,?_⟩
 intro g
 rw [values,FIz_PublicDigest.value]
 exact fold _ _ _ g
#print axioms fold
#print axioms source
end AspisR1.NKR_DigestOldPack
end
