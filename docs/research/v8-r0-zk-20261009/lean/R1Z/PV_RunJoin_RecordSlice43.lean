import R1Z.PV_RunJoin_ByteExtension43
import R1Z.PV_RunJoin_HighDomain40
set_option autoImplicit false
namespace R1Z.PV_RunJoin_RecordSlice43
open Aeneas Aeneas.Std

theorem payload (before header body tail : List U8) (hlen : header.length=5) :
    (((before++header++body)++tail).drop (before.length+5)).take body.length=body := by
  rw [List.append_assoc before header body,List.append_assoc before (header++body) tail,
    List.drop_append]
  simp only [Nat.add_sub_cancel_left,List.drop_eq_nil_of_le (by omega : before.length≤before.length+5),
    List.nil_append]
  rw [List.append_assoc header body tail,List.drop_append]
  rw [List.drop_eq_nil_of_le (by omega : header.length≤5),hlen,Nat.sub_self,
    List.drop_zero,List.nil_append]
  simp only [List.take_append,List.take_length,Nat.sub_self,List.take_zero,List.append_nil]

theorem preserved (before tail : List U8) (at1 size : Nat) (bound : at1+size≤before.length) :
    (((before++tail).drop at1).take size)=(before.drop at1).take size := by
  rw [List.drop_append]
  have h : at1≤before.length := by omega
  rw [Nat.sub_eq_zero_of_le h,List.drop_zero,List.take_append]
  have hsize : size≤(before.drop at1).length := by rw [List.length_drop];omega
  rw [Nat.sub_eq_zero_of_le hsize,List.take_zero,List.append_nil]

#print axioms payload
#print axioms preserved
end R1Z.PV_RunJoin_RecordSlice43
