import R1Z.PV_RDEAC_NibbleBounds
open Aeneas Aeneas.Std Result
namespace R1Z.PV_RDEAC_DigitText
open PV_RDEA_ActualDigitTable PV_RDEAC_AppendSimulation

def text (i : Fin 16) : String :=
  ["0","1","2","3","4","5","6","7","8","9","a","b","c","d","e","f"][i.val]'(by exact i.isLt)

def entry (i : Fin 16) : Str := table.val[i.val]'(by exact i.isLt)

theorem one_byte_values (bs : ByteArray) (h : bs.size=1) : bs.toList=[bs.get! 0] := by
  unfold ByteArray.toList
  rw [ByteArray.toList.loop]
  simp only [h,Nat.zero_lt_succ,if_true]
  rw [ByteArray.toList.loop]
  simp only [h,Nat.lt_irrefl,if_false]
  rfl

theorem bytes (i : Fin 16) : (entry i).val=PV_CBL_StringBytesAdapter.encodeList (text i) := by
  fin_cases i <;> simp only [entry,text,table,Array.make,List.getElem_cons_zero,List.getElem_cons_succ,toStr]
  all_goals rw [one_byte_values _ (by rw [String.size_toByteArray]; rfl)]
  all_goals rfl

theorem length (i : Fin 16) : (entry i).val.length=1 := entry_length i

theorem lookup (i : Usize) (h : i.val<16) :
    Array.index_usize table i=ok (entry ⟨i.val,h⟩) := by
  unfold Array.index_usize
  simp only [Array.getElem?_Usize_eq]
  rw [List.getElem?_eq_getElem (by exact h)]
  rfl

#print axioms one_byte_values
#print axioms bytes
#print axioms length
#print axioms lookup
end R1Z.PV_RDEAC_DigitText
