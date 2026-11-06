import NKR_TermSemanticCut
set_option autoImplicit false
noncomputable section
namespace AspisR1.NKR_TermSemanticCut
open Aeneas Aeneas.Std Result FIq_Native
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (Canon decode)
open FIw_ArrayValue (canonical decoded)
open NKI_InitialPrefix (Public Openings Selectors)
open NKR_TermSemanticSource (Packed)

theorem digest_source (pub : Public) (o : Openings) (s : Selectors) (before : Packed) (digests : Pair)
 (hb : canonical before) (hd : ∀ j,Canon (digests j)) :
 ∃ (replies : Pair) (out : Packed),digest_reference before digests=ok out ∧ canonical out ∧
 (∀ g : Fin 2,field.QM31.add (NJB_ArrayCarrier.cell before (if g.val=0 then ⟨21,by decide⟩ else ⟨22,by decide⟩)) (digests g)=ok (replies g)) ∧
 DigestCut pub o s before digests replies (digestObservation pub o s before out digests) ∧
 ∀ g : Fin 2,decode (replies g)=decode (NJB_ArrayCarrier.cell before (if g.val=0 then ⟨21,by decide⟩ else ⟨22,by decide⟩))+decode (digests g) := by
 obtain ⟨a,ca,ha,va⟩:=NJB_StubLaws.qm_add (NJB_ArrayCarrier.cell before ⟨21,by decide⟩) (digests 0) (NJB_ArrayCarrier.canonical_cell before hb _) (hd 0)
 obtain ⟨b,cb,hb',vb⟩:=NJB_StubLaws.qm_add (NJB_ArrayCarrier.cell before ⟨22,by decide⟩) (digests 1) (NJB_ArrayCarrier.canonical_cell before hb _) (hd 1)
 let replies : Pair:=![a,b]
 let out:=NJB_ArrayCarrier.array (digestFrame before replies)
 have co : canonical out := NJB_ArrayCarrier.canonical_array _ (fun j=>by
  unfold digestFrame
  split
  · exact ha
  · split
    · exact hb'
    · exact NJB_ArrayCarrier.canonical_cell before hb j)
 refine ⟨replies,out,?_,co,?_,?_,?_⟩
 · simp only [digest_reference,ca,cb,bind_tc_ok]
   rfl
 · intro g;fin_cases g
   · exact ca
   · exact cb
 · exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,fun j=>congrFun (NJB_ArrayCarrier.cell_array (digestFrame before replies)) j⟩
 · intro g;fin_cases g
   · exact va
   · exact vb
#print axioms digest_source
end AspisR1.NKR_TermSemanticCut
end
