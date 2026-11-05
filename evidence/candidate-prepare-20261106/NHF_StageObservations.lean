import NHF_Overwrite
set_option autoImplicit false
noncomputable section
namespace AspisR1.NHF_StageObservations
open Aeneas Aeneas.Std Result NGV_ByteWindow
/-- Relative scalar source window used by the native local-record cuts. -/
def sourceIndex (r cell : Nat) : Option Nat :=
 if cell<5 then some cell else if r<14 then some cell else
 if (cell-5)%32<16 then some (5+(cell-5)/32*16+(cell-5)%32) else none

def rowByte (input : Slice U8) (r cell : Nat) : U8 :=
 match sourceIndex r cell with
 | none => 0#u8
 | some local => input.val[NGD_SemanticSchedule.src r+local]?.getD 0#u8

/-- The selected byte index lies in the SAME framed source field. -/
theorem source_domain (r cell local : Nat) (live : r<27)
 (cellBound : cell<5+NFU_PacketDomains.payloadSize r)
 (selected : sourceIndex r cell=some local) : local<5+NGD_SemanticSchedule.stored r := by
 unfold sourceIndex at selected
 split at selected
 · cases selected
   have h:=NGD_SemanticSchedule.windows r live
   omega
 · split at selected
   · cases selected
     simp only [NGD_SemanticSchedule.stored,if_neg (by omega : ¬14≤r)]
     exact cellBound
   · split at selected
     · cases selected
       have h:=NGD_SemanticSchedule.expansion_domain r (by omega) live
       omega
     · cases selected

/-- Exact source law paired with native row-window logging stubs. -/
theorem payload (input : Slice U8) (r j : Nat) (live : r<27)
 (within : j<NFU_PacketDomains.payloadSize r) :
 NGV_SemanticValues.payloadByte input r j = rowByte input r (5+j) := by
 have atLeast : ¬5+j<5 := by omega
 have back : 5+j-5=j := by omega
 unfold rowByte sourceIndex
 simp only [if_neg atLeast,back]
 by_cases low:r<14
 · simp only [NGV_SemanticValues.payloadByte,if_pos low]
   simp only [Option.some.injEq]
   congr 2 <;> omega
 · simp only [NGV_SemanticValues.payloadByte,if_neg low]
   unfold NFU_Retarget.LPl_A.Expand.byte
   split
   · have valid : j/32*16+j%32<NGD_SemanticSchedule.stored r := by
       have h:=NGD_SemanticSchedule.expansion_domain r (by omega) live
       omega
     simp only [NGV_RowPayload.source,select,List.getElem?_take,if_pos valid,List.getElem?_drop]
     congr 2 <;> omega
   · rfl
/-- The caller's exact7015-byte original proof window supplies that scalar
byte; it is never an independently selected buffer or an assumed output. -/
theorem original_byte (proof : Slice U8) (r cell local : Nat)
 (live : r<27) (selected : sourceIndex r cell=some local)
 (cellBound : cell<5+NFU_PacketDomains.payloadSize r) :
 rowByte (select proof 16 7015) r cell =
 proof.val[16+NGD_SemanticSchedule.src r+local]?.getD 0#u8 := by
 have localBound:=source_domain r cell local live cellBound selected
 have bounds:=NGD_SemanticSchedule.windows r live
 have within : NGD_SemanticSchedule.src r+local<7015 := by omega
 simp only [rowByte,selected,select,List.getElem?_take,if_pos within,List.getElem?_drop]
 congr 2 <;> omega

/-- Complete callee producer and every native row-window value, constructed
from the same input and arbitrary prestate. -/
theorem semantic (input before : Slice U8) (inputSize : input.val.length=7015)
 (outputSize : before.val.length=13831) :
 ∃ after : Slice U8,
 AspisS1NativeCompact.compact.expand_semantic AspisS1ValuesOwnedInstallation.nativeValues input before=
   ok (.Ok (),after) ∧ after.val.length=13831 ∧
 (∀ j,j<32→after.val[j]?=input.val[j]?) ∧
 (∀ r,r<27→∀ cell,cell<5+NFU_PacketDomains.payloadSize r→
  after.val[NGD_SemanticSchedule.dst r+cell]?.getD 0#u8=rowByte input r cell) := by
 obtain ⟨after,run,_,size,head,rows⟩:=NGV_SemanticPacket.result input before inputSize outputSize
 refine ⟨after,run,size,head,?_⟩
 intro r live cell within
 by_cases first:cell<5
 · have h:=(rows r live).1 cell first
   simpa only [rowByte,sourceIndex,if_pos first] using congrArg (fun x : Option U8=>x.getD 0#u8) h
 · have back : 5+(cell-5)=cell := by omega
   have h:=(rows r live).2 (cell-5) (by omega)
   rw [payload input r (cell-5) live (by omega)] at h
   simpa only [Nat.add_assoc,back] using h
#print axioms source_domain
#print axioms payload
#print axioms original_byte
#print axioms semantic
end AspisR1.NHF_StageObservations
end
