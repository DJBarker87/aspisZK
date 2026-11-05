import NHF_Expansions
set_option autoImplicit false
noncomputable section
namespace AspisR1.NHF_Overwrite
open Aeneas Aeneas.Std Result
/-- Extensionality for complete byte observations, with no zero-default gaps. -/
theorem ext (left right : Slice U8) (size : left.val.length=right.val.length)
 (bytes : ∀ j,j<left.val.length→left.val[j]?.getD 0#u8=right.val[j]?.getD 0#u8) : left=right := by
 apply Subtype.ext
 apply List.ext_getElem
 · exact size
 · intro j hj hk
   have same:=bytes j hj
   simpa only [List.getElem?_eq_getElem hj,List.getElem?_eq_getElem hk,Option.getD_some] using same
/-- Semantic expansion overwrites every byte. Its complete produced value is
independent of arbitrary prior output contents; no initialized-zero premise. -/
theorem semantic (input before₁ before₂ : Slice U8)
 (inputSize : input.val.length=7015)
 (firstSize : before₁.val.length=13831) (secondSize : before₂.val.length=13831) :
 ∃ after : Slice U8,
 AspisS1NativeCompact.compact.expand_semantic AspisS1ValuesOwnedInstallation.nativeValues input before₁=
   ok (.Ok (),after) ∧
 AspisS1NativeCompact.compact.expand_semantic AspisS1ValuesOwnedInstallation.nativeValues input before₂=
   ok (.Ok (),after) := by
 obtain ⟨a,callA,_,lenA,headA,rowsA⟩:=NGV_SemanticPacket.result input before₁ inputSize firstSize
 obtain ⟨b,callB,_,lenB,headB,rowsB⟩:=NGV_SemanticPacket.result input before₂ inputSize secondSize
 have same : a=b := by
   apply ext a b (lenA.trans lenB.symm)
   intro j inside
   rcases NGV_SemanticPacket.coverage j (by omega) with first | ⟨r,live,start,finish⟩
   · exact congrArg (fun x : Option U8=>x.getD 0#u8) ((headA j first).trans (headB j first).symm)
   · by_cases header:j<NGD_SemanticSchedule.dst r+5
     · have offset : NGD_SemanticSchedule.dst r+(j-NGD_SemanticSchedule.dst r)=j := by omega
       have ha:=(rowsA r live).1 (j-NGD_SemanticSchedule.dst r) (by omega)
       have hb:=(rowsB r live).1 (j-NGD_SemanticSchedule.dst r) (by omega)
       rw [offset] at ha hb
       exact congrArg (fun x : Option U8=>x.getD 0#u8) (ha.trans hb.symm)
     · have offset : NGD_SemanticSchedule.dst r+5+(j-(NGD_SemanticSchedule.dst r+5))=j := by omega
       have ha:=(rowsA r live).2 (j-(NGD_SemanticSchedule.dst r+5)) (by omega)
       have hb:=(rowsB r live).2 (j-(NGD_SemanticSchedule.dst r+5)) (by omega)
       rw [offset] at ha hb
       exact ha.trans hb.symm
 subst b
 exact ⟨a,callA,callB⟩
/-- The right expansion similarly overwrites all928 bytes on the exact caller
input464, including every zero high half. -/
theorem values (input before₁ before₂ : Slice U8)
 (inputSize : input.val.length=464) (firstSize : before₁.val.length=928) (secondSize : before₂.val.length=928) :
 ∃ after : Slice U8,
 NFU_Retarget.compact.expand_values input before₁=ok (.Ok (),after) ∧
 NFU_Retarget.compact.expand_values input before₂=ok (.Ok (),after) := by
 obtain ⟨a,callA,_,lenA,bytesA⟩:=NGV_ExpandAssociation.result input before₁
   (by omega) (by rw [inputSize]) (by rw [inputSize,firstSize])
 obtain ⟨b,callB,_,lenB,bytesB⟩:=NGV_ExpandAssociation.result input before₂
   (by omega) (by rw [inputSize]) (by rw [inputSize,secondSize])
 have same : a=b := by
   apply ext a b (by omega)
   intro j live
   exact (bytesA j (by omega)).trans (bytesB j (by omega)).symm
 subst b
 exact ⟨a,callA,callB⟩
#print axioms ext
#print axioms semantic
#print axioms values
end AspisR1.NHF_Overwrite
end
