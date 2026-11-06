import NKR_DigestRegularValue
set_option autoImplicit false
noncomputable section
namespace AspisR1.NKR_DigestKeyValues
open Aeneas Aeneas.Std Result
open FIv_NativeValue (Canon decode K)
open NKI_InitialPrefix (Public Openings Selectors)
open NKR_DigestChildren (Children Clauses)

def term (p : Public) (o : Openings) (s : Selectors) (key : R0P.DigestKey) (g : Fin 2) : K :=
 NKR_DigestOldPack.contribution (FIw_PublicModel.ofPublic p) (FIw_PublicModel.openings o) (FIw_PublicModel.selector s) key g

theorem ordinary (p : Public) (o : Openings) (s : Selectors) (c : Children)
 (hp : NKR_DigestChildren.Domain p) (ho : FIw_ArrayValue.canonical o.z)
 (hh : FIw_ArrayValue.canonical s.high) (hc : Clauses p o s c) (g : Fin 2) :
 term p o s .anchor g=FIv_NativeArray.value s.low 11*decode (c.anchor g) ∧
 term p o s .nullifier g=FIv_NativeArray.value s.low 11*decode (c.nullifier g) ∧
 term p o s .change g=FIv_NativeArray.value s.low 11*decode (c.change g) ∧
 term p o s .nextRoot g=FIv_NativeArray.value s.low 11*decode (c.nextRoot g) := by
 obtain ⟨_,am,_,nm,_,_,_,dm,_,_,rootm,_⟩ := hc
 have av:=NKR_DigestRegularValue.scaled_cohort s o 56 p.anchor c.anchor hh ho hp.anchor am g
 have nv:=NKR_DigestRegularValue.scaled_cohort s o 26 p.nullifier c.nullifier hh ho hp.nullifier nm g
 have dv:=NKR_DigestRegularValue.scaled_cohort s o 32 p.change c.change hh ho hp.change dm g
 have rv:=NKR_DigestRegularValue.scaled_cohort s o 53 p.transition.candidate_afterstate.next_root c.nextRoot hh ho hp.nextRoot rootm g
 constructor
 · exact (show term p o s .anchor g=NKR_DigestRegularValue.binding s o.z 56 p.anchor g from rfl).trans av
 constructor
 · exact (show term p o s .nullifier g=NKR_DigestRegularValue.binding s o.z 26 p.nullifier g from rfl).trans nv
 constructor
 · exact (show term p o s .change g=NKR_DigestRegularValue.binding s o.z 32 p.change g from rfl).trans dv
 · exact (show term p o s .nextRoot g=NKR_DigestRegularValue.binding s o.z 53 p.transition.candidate_afterstate.next_root g from rfl).trans rv

#print axioms ordinary
end AspisR1.NKR_DigestKeyValues
end
