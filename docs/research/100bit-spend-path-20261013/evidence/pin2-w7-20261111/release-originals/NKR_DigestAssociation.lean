import NKR_DigestComplete
import NKR_DigestFrontierSum
import NKR_DigestOptionalValue
set_option autoImplicit false
noncomputable section
namespace AspisR1.NKR_DigestAssociation
open Aeneas Aeneas.Std Result
open FIv_NativeValue (decode K)
open NKI_InitialPrefix (Public Openings Selectors)
open NKR_DigestChildren (Children Clauses)
open NKR_DigestKeyValues (term)

theorem keys (p : Public) :
 R0P.digestKeys (FIw_PublicModel.ofPublic p)=
 [.anchor,.nullifier]++NKR_DigestOptionalValue.recipientKeys p++[.change]++
 List.ofFn R0P.DigestKey.frontier++[.nextRoot]++NKR_DigestOptionalValue.carryKeys p := by
 unfold R0P.digestKeys FIw_PublicModel.ofPublic NKR_DigestOptionalValue.recipientKeys NKR_DigestOptionalValue.carryKeys
 cases p.recipient <;> rfl

/-- Complete optimized expression equals the packed adopted cohort's call
sum. All SAME-call clauses are internal support, discharged by the root. -/
theorem model (p : Public) (o : Openings) (s : Selectors) (c : Children)
 (hp : NKR_DigestChildren.Domain p) (ho : FIw_ArrayValue.canonical o.z)
 (hh : FIw_ArrayValue.canonical s.high) (hc : Clauses p o s c) (g : Fin 2) :
 NKR_DigestComplete.model s c g=
 ((R0P.digestKeys (FIw_PublicModel.ofPublic p)).map (fun key=>term p o s key g)).sum := by
 obtain ⟨anchor,nullifier,change,nextRoot⟩ := NKR_DigestKeyValues.ordinary p o s c hp ho hh hc g
 have recipient:=NKR_DigestOptionalValue.recipient p o s c hp ho hh hc g
 have carry:=NKR_DigestOptionalValue.carry p o s c hp ho hh hc g
 have frontier:=NKR_DigestFrontierSum.source p o s c hp ho hh hc g
 rw [keys]
 simp only [List.map_append,List.sum_append,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero]
 rw [anchor,nullifier,change,nextRoot,recipient,carry,frontier]
 have w0 : decode (NKI_LowMixCaller.low s 0)=FIv_NativeArray.value s.low 0 := NKR_DigestReads.cell _ _
 have w11 : decode (NKI_LowMixCaller.low s 1)=FIv_NativeArray.value s.low 11 := NKR_DigestReads.cell _ _
 have w12 : decode (NKI_LowMixCaller.low s 2)=FIv_NativeArray.value s.low 12 := NKR_DigestReads.cell _ _
 unfold NKR_DigestComplete.model NKR_DigestAppendValue.low0 NKR_DigestAppendValue.low12
 rw [w0,w11,w12]
 ring
#print axioms keys
#print axioms model
end AspisR1.NKR_DigestAssociation
end
