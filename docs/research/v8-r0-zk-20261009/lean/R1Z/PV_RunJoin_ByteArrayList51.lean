import R1Z.PV_RunJoin_TranscriptFrames51
set_option autoImplicit false
namespace R1Z.PV_RunJoin_ByteArrayList51

theorem loop (bs : ByteArray) (i : Nat) (acc : List UInt8) :
    ByteArray.toList.loop bs i acc=acc.reverse++bs.data.toList.drop i := by
  fun_induction ByteArray.toList.loop bs i acc with
  | case1 i acc hi ih =>
    rw [ih,List.reverse_cons,List.append_assoc]
    congr 1
    have hlen : i<bs.data.toList.length := by simpa using hi
    have eq : bs.get! i=bs.data.toList[i]'hlen := by
      simp [ByteArray.get!,hi,ByteArray.getElem_eq_getElem_data]
      rfl
    rw [eq]
    exact (List.cons_getElem_drop_succ (l:=bs.data.toList) (i:=i) (h:=hlen)).symm
  | case2 i acc hi =>
    have bound : bs.data.toList.length ≤ i := by simpa using Nat.le_of_not_gt hi
    rw [List.drop_eq_nil_of_le bound,List.append_nil]

theorem complete (bs : ByteArray) : bs.toList=bs.data.toList := by
  unfold ByteArray.toList
  rw [loop]
  rfl

theorem of_list (xs : List UInt8) : xs.toByteArray.toList=xs := by
  rw [complete,List.toList_data_toByteArray]
#print axioms loop
#print axioms complete
#print axioms of_list
end R1Z.PV_RunJoin_ByteArrayList51
