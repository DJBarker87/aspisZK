import NKR_TermSemanticCut
import NJX_DigestGroups
set_option autoImplicit false
noncomputable section
namespace AspisR1.NKR_TermDigestFrame
open Aeneas Aeneas.Std Result FIq_Native
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (Canon decode K)
open FIw_ArrayValue (canonical decoded)
open NKI_InitialPrefix (Public Openings Selectors)
open NKR_TermSemanticSource (Packed)
open NKR_TermSemanticCut (Pair)

def packed (old : Array NQ 8#usize) (g : Fin 2) : K :=
 NJB_PackLinearity.pack (fun j=>decoded old (NJX_DigestGroups.index g j))

/-- Preweighted84's whole24cell footprint is exactly groups21 and22. The
other22cells vanish symbolically; no concrete whole-array reduction is used. -/
theorem increment (old : Array NQ 8#usize) (j : Fin (24#usize).val) :
 FIx_SelectedMeaning.contribution (decoded old) 84 j.val=
 if j.val=21 then packed old 0 else if j.val=22 then packed old 1 else 0 := by
 by_cases h21 : j.val=21
 · rw [if_pos h21]
   unfold FIx_SelectedMeaning.contribution packed
   change FIx_PreweightedPack.pack _=FIx_PreweightedPack.pack _
   congr 1
   funext lane
   unfold FIx_SelectedMeaning.selected
   have h:=lane.isLt
   rw [dif_pos (by constructor <;> omega)]
   apply congrArg (decoded old)
   apply Fin.ext
   simp only [NJX_DigestGroups.index,Fin.val_zero]
   omega
 · rw [if_neg h21]
   by_cases h22 : j.val=22
   · rw [if_pos h22]
     unfold FIx_SelectedMeaning.contribution packed
     change FIx_PreweightedPack.pack _=FIx_PreweightedPack.pack _
     congr 1
     funext lane
     unfold FIx_SelectedMeaning.selected
     have h:=lane.isLt
     rw [dif_pos (by constructor <;> omega)]
     apply congrArg (decoded old)
     apply Fin.ext
     simp only [NJX_DigestGroups.index,Fin.val_one]
     omega
   · rw [if_neg h22]
     unfold FIx_SelectedMeaning.contribution
     have cells : (fun lane : Fin (4#usize).val=>FIx_SelectedMeaning.selected (decoded old) 84 j.val lane.val)=fun _=>0 := by
      funext lane
      unfold FIx_SelectedMeaning.selected
      have hl:=lane.isLt
      rw [dif_neg (by omega)]
     rw [cells]
     simp only [FIx_PreweightedPack.pack,mul_zero,add_zero]

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
 rcases cut with ⟨_,_,_,_,_,_,frame⟩
 have directValue (j : Fin (24#usize).val) : decoded out j=decoded before j+
  (if j.val=21 then packed old 0 else if j.val=22 then packed old 1 else 0) := by
  change decode (NJB_ArrayCarrier.cell out j)=_
  rw [frame j]
  by_cases h21 : j.val=21
  · have same : j=⟨21,by decide⟩:=Fin.ext h21
    subst j
    simp only [NKR_TermSemanticCut.digestFrame,ite_true]
    rw [value 0,pairing 0]
  · by_cases h22 : j.val=22
    · have same : j=⟨22,by decide⟩:=Fin.ext h22
      subst j
      simp only [NKR_TermSemanticCut.digestFrame,show ¬(22:Nat)=21 from by decide,ite_false,ite_true]
      rw [value 1,pairing 1]
    · simp only [NKR_TermSemanticCut.digestFrame,if_neg h21,if_neg h22,add_zero]
 have same : out=oldOut := NKI_ArrayCanonicalEq.source out oldOut co cold (by
  funext j
  rw [directValue j,oldValue j,increment old j])
 exact ⟨out,direct,by rw [oldCall,←same],co⟩
#print axioms increment
#print axioms source
end AspisR1.NKR_TermDigestFrame
end
