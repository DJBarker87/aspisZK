import NKR_TermDigestSupport
import NJX_DigestGroups
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLH_TermDigestFrame
open Aeneas Aeneas.Std Result FIq_Native
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (Canon decode K)
open FIw_ArrayValue (canonical decoded)
open NKI_InitialPrefix (Public Openings Selectors)
open NKR_TermSemanticSource (Packed)
open NKR_TermSemanticCut (Pair)
open NKR_TermDigestFrame (increment)
abbrev packed := NKR_TermDigestFrame.packed

/-- Generic native-to-source261 digest window association. The packing
clause is SUPPORT input: the261 ROOT must discharge it from SAME250/251
child outputs; it is never retained as a positive root endpoint premise. -/
theorem source (pub : Public) (o : Openings) (s : Selectors) (before : Packed)
 (old : Array NQ 8#usize) (digests : Pair)
 (hb : canonical before) (ho : canonical old) (hd : ∀ g,Canon (digests g))
 (pairing : ∀ g,decode (digests g)=packed old g) :
 ∃ out,NKR_TermSemanticCut.digest_reference before digests=ok out ∧
 pool_v1.pair_forest_semantic_terminal.add_preweighted before 84#usize old=ok out ∧ canonical out := by
 obtain ⟨replies,out,direct,co,calls,cut,value⟩:=NKR_TermSemanticCut.digest_source pub o s before digests hb hd
 obtain ⟨oldOut,oldCall,cold,oldValue⟩:=NHU_Preweighted.result before 84#usize old (by decide) (by decide) hb ho
 rcases cut with ⟨_,_,_,_,_,_,observedFrame⟩
 have frame (j : Fin (24#usize).val) : NJB_ArrayCarrier.cell out j=NKR_TermSemanticCut.digestFrame before replies j :=
  observedFrame j
 have directValue (j : Fin (24#usize).val) : decoded out j=decoded before j+
  (if j.val=21 then packed old 0 else if j.val=22 then packed old 1 else 0) := by
  change decode (NJB_ArrayCarrier.cell out j)=_
  erw [frame j]
  by_cases h21 : j.val=21
  · have same : j=⟨21,by decide⟩:=Fin.ext h21
    subst j
    simp only [NKR_TermSemanticCut.digestFrame,ite_true]
    erw [value 0,pairing 0]
    rfl
  · by_cases h22 : j.val=22
    · have same : j=⟨22,by decide⟩:=Fin.ext h22
      subst j
      simp only [NKR_TermSemanticCut.digestFrame,show ¬(22:Nat)=21 from by decide,ite_false,ite_true]
      erw [value 1,pairing 1]
      rfl
    · simp only [NKR_TermSemanticCut.digestFrame,if_neg h21,if_neg h22,add_zero]
      rfl
 have same : out=oldOut := NKI_ArrayCanonicalEq.source out oldOut co cold (by
  funext j
  erw [directValue j,oldValue j,increment old j])
 exact ⟨out,direct,by rw [oldCall,←same],co⟩
#print axioms source
end AspisR1.NLH_TermDigestFrame
end
