import R1Z.PV_OWNB_Cursor
import Init.Data.List.Range
set_option autoImplicit false
namespace R1Z.PV_OWNB_Prefix
open PV_OWNB_Cursor PV_OWN_Link
def values (q : Cursor) : List Link := (List.range q.written).map q.output

theorem length (q : Cursor) : (values q).length=q.written := by simp [values]

theorem advance (q : Cursor) : values (PV_OWNB_Cursor.advance q)=values q := rfl

theorem sink (q : Cursor) (v : Link) : values (PV_OWNB_Cursor.sink q v)=values q++[v] := by
 unfold values PV_OWNB_Cursor.sink
 dsimp only
 rw [List.range_succ,List.map_append]
 simp only [List.map_cons,List.map_nil,ite_true]
 congr 1
 apply List.map_congr_left
 intro i hi
 have small:i<q.written := List.mem_range.mp hi
 have ne:i≠q.written := by omega
 simp [ne]
#print axioms length
#print axioms advance
#print axioms sink
end R1Z.PV_OWNB_Prefix
