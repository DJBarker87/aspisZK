import NGV_ByteWindow
import NGV_ExpandAssociation
import NGV_SemanticDomains
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace NGV_RowPayload
open NGV_ByteWindow
def source (input : Slice U8) (r : Nat) : Slice U8 :=
 select input (NGD_SemanticSchedule.src r+5) (NGD_SemanticSchedule.stored r)
def middle (input before : Slice U8) (r : Nat) : Slice U8 :=
 write before (NGD_SemanticSchedule.dst r) (select input (NGD_SemanticSchedule.src r) 5)
def target (input before : Slice U8) (r : Nat) : Slice U8 :=
 select (middle input before r) (NGD_SemanticSchedule.dst r+5) (NFU_PacketDomains.payloadSize r)
structure Packet (input before : Slice U8) (r : Nat) where
 value : Slice U8
 size : value.val.length=NFU_PacketDomains.payloadSize r
 low : r<14 → value=source input r
 native : 14≤r → NFU_Retarget.compact.expand_values (source input r) (target input before r)=ok (.Ok (),value)
 adopted : 14≤r → AspisS1ValuesOwnedInstallation.expandValues (source input r) (target input before r)=ok (.Ok (),value)
 bytes : 14≤r → ∀ j,j<NFU_PacketDomains.payloadSize r → value.val[j]?.getD 0#u8=
   NFU_Retarget.LPl_A.Expand.byte (source input r).val j
def after {input before : Slice U8} {r : Nat} (packet : Packet input before r) : Slice U8 :=
 write (middle input before r) (NGD_SemanticSchedule.dst r+5) packet.value
theorem domains (input before : Slice U8) (r : Nat) (live : r<27)
 (inputSize : input.val.length=7015) (outputSize : before.val.length=13831) :
 (source input r).val.length=NGD_SemanticSchedule.stored r ∧
 (target input before r).val.length=NFU_PacketDomains.payloadSize r := by
 have bounds:=NGD_SemanticSchedule.windows r live
 constructor
 · apply select_length;omega
 · apply select_length
   have kept:=write_length before (select input (NGD_SemanticSchedule.src r) 5) (NGD_SemanticSchedule.dst r)
   change NGD_SemanticSchedule.dst r+5+NFU_PacketDomains.payloadSize r≤(middle input before r).val.length
   unfold middle;rw [kept];omega
theorem construct (input before : Slice U8) (r : Nat) (live : r<27)
 (inputSize : input.val.length=7015) (outputSize : before.val.length=13831) :
 Nonempty (Packet input before r) := by
 obtain ⟨sourceLength,targetLength⟩:=domains input before r live inputSize outputSize
 by_cases high : 14≤r
 · obtain ⟨alignment,doubling⟩:=NGD_SemanticSchedule.expansion_domain r high live
   obtain ⟨value,native,adopted,size,bytes⟩:=NGV_ExpandAssociation.result
     (source input r) (target input before r)
     (by rw [sourceLength];exact (NGD_SemanticSchedule.windows r live).2.2.1)
     (by rw [sourceLength];exact alignment) (by rw [sourceLength,targetLength];exact doubling)
   exact ⟨⟨value,size.trans targetLength,fun low=>by omega,fun _=>native,fun _=>adopted,
     fun _ j hj=>bytes j (by rw [targetLength];exact hj)⟩⟩
 · have low : r<14 := by omega
   have stored : NGD_SemanticSchedule.stored r=NFU_PacketDomains.payloadSize r := by
     simp only [NGD_SemanticSchedule.stored,if_neg high]
   exact ⟨⟨source input r,sourceLength.trans stored,fun _=>rfl,
     fun h=>by omega,fun h=>by omega,fun h=>by omega⟩⟩
theorem length {input before : Slice U8} {r : Nat} (packet : Packet input before r) :
 packet.after.val.length=before.val.length := by
 unfold after middle
 rw [write_length,write_length]
#print axioms domains
#print axioms construct
#print axioms length
end NGV_RowPayload
