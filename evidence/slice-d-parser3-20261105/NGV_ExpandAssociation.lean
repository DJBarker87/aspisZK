import NGV_ExpandPacket
import NGK_COMBINED_IMPORT
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace NGV_ExpandAssociation
open NFU_Retarget
/-- Complete closed-callee carrier association on the SAME arbitrary window.
The adopted owned reference's total formula is retained, not re-proved. -/
theorem result (bytes before : Slice U8)
 (bound : bytes.val.length≤1856) (aligned : bytes.val.length%16=0)
 (shape : before.val.length=2*bytes.val.length) :
 ∃ after : Slice U8,
 NFU_Retarget.compact.expand_values bytes before=ok (.Ok (),after) ∧
 AspisS1ValuesOwnedInstallation.expandValues bytes before=ok (.Ok (),after) ∧
 after.val.length=before.val.length ∧
 (∀ j,j<before.val.length→after.val[j]?.getD 0#u8=LPl_A.Expand.byte bytes.val j) := by
 obtain ⟨native,nativeRun,nativeLength,nativeBytes⟩:=NGV_ExpandPacket.result bytes before bound aligned shape
 obtain ⟨model,modelRun,modelLength,modelBytes⟩:=AspisS1ValuesOwnedExact.installed_exact
   bytes before aligned shape (by scalar_tac)
 have same : native=model := by
   apply Subtype.ext
   apply List.ext_getElem
   · exact nativeLength.trans modelLength.symm
   · intro j hj hk
     have hn:=nativeBytes j (by omega)
     have hm:=congrArg (fun x : Option U8=>x.getD 0#u8) (modelBytes j hk)
     have eq : native.val[j]?.getD 0#u8=model.val[j]?.getD 0#u8 := by
       rw [hn,hm]
       unfold LPl_A.Expand.byte
       split <;> rfl
     simpa only [List.getElem?_eq_getElem hj,List.getElem?_eq_getElem hk,Option.getD_some] using eq
 refine ⟨native,nativeRun,?_,nativeLength,nativeBytes⟩
 simpa only [same] using modelRun
#print axioms result
end NGV_ExpandAssociation
