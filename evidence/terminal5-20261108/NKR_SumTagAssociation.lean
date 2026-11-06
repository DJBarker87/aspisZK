import NKR_SumCopyCollect
import NKR_SumTagPermutation
import NKR_SumLookupCertificate
import NJL_TagMeaning
set_option autoImplicit false
noncomputable section
namespace AspisR1.NKR_SumTagAssociation
open Aeneas Aeneas.Std
open FIv_NativeValue (K decode)
open NKR_SumTagPermutation (Domain index side tag)
open NKR_SumCopyCollect (Lookups)

/-- Remaining exact assertions of NKR_tag_metadata_cut,transcribed on the
model's pinned tag/descriptor arrays. The oldNJLtagregistry cut binds those
arrays to frozen constants and the oldNJLlookup cut binds gc to actualsource
lookup. No field value or composed endpoint equality is asserted here. -/
structure Cut (domain : Domain) : Prop where
 tag : ∀ t,NKR_SumTagPermutation.tag t=(NJL_EndpointLookup.link (index domain t)).tag.val
 block : ∀ t,(NJL_TagData.block t).val=NJL_EndpointLookup.row (index domain t) (side t)/16
 coordinate : ∀ (c : Fin 30) (t : Fin 272),t∈NJL_TagData.indices c →
  NJL_EndpointLookup.gc (index domain t) (side t)=c.val

theorem high (domain : Domain) (cut : Cut domain) (lookup : Lookups)
 (s : FIq_Native.pool_v1.pair_forest_copy_terminal.Selectors) (t : Fin 272) :
 NJB_ActiveReference.high s (NJL_TagData.block t)=
 NJL_EndpointLookup.high s (index domain t) (side t) (lookup (index domain t) (side t)) := by
 have block : NJL_TagData.block t=NJL_EndpointLookup.block (index domain t) (side t)
  (lookup (index domain t) (side t)) := Fin.ext (cut.block t)
 exact congrArg (NJB_ActiveReference.high s) block

theorem term (domain : Domain) (cut : Cut domain) (lookup : Lookups)
 (s : FIq_Native.pool_v1.pair_forest_copy_terminal.Selectors) (t : Fin 272) :
 decode (NJB_ActiveReference.high s (NJL_TagData.block t))*(NJL_TagData.tag t).val=
 decode (NJL_EndpointLookup.high s (index domain t) (side t) (lookup (index domain t) (side t)))*
 (NJL_EndpointLookup.link (index domain t)).tag.val := by
 rw [high domain cut lookup s t]
 have value := cut.tag t
 change (NJL_TagData.tag t).val=_ at value
 rw [value]

theorem coordinate (domain : Domain) (cut : Cut domain) (lookup : Lookups)
 (c : Fin 30) (t : Fin 272) (ht : t∈NJL_TagData.indices c) :
 NJL_EndpointLookup.groupIndex (index domain t) (side t) (lookup (index domain t) (side t))=c :=
 Fin.ext (cut.coordinate c t ht)

/-- The actual low-selector index of each frozen tag term is its endpoint's
row&15 (equivalentlyrow%16),derived from the reviewed scan/keycertificate. -/
theorem low (domain : Domain) (cut : Cut domain) (lookup : Lookups)
 (keys : ∀ i consumer,NKR_SumLookupCertificate.Cut i consumer)
 (c : Fin 30) (t : Fin 272) (ht : t∈NJL_TagData.indices c) :
 (NKR_SumFinishData.low c).val=NJL_EndpointLookup.row (index domain t) (side t)%16 := by
 have key := (NKR_SumLookupCertificate.keys (index domain t) (side t)
  (lookup (index domain t) (side t)) (keys (index domain t) (side t))).1
 rw [coordinate domain cut lookup c t ht] at key
 have out := congrArg Prod.snd key
 exact out.trans (NKR_SumLookupCertificate.column_mod _ _)

#print axioms high
#print axioms term
#print axioms coordinate
#print axioms low
end AspisR1.NKR_SumTagAssociation
end
