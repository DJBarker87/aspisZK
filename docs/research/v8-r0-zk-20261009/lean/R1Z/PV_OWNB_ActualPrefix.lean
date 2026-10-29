import R1Z.PV_OWNB_Prefix
import R1Z.PV_OWNB_ActualSink
set_option autoImplicit false
namespace R1Z.PV_OWNB_ActualPrefix
open PV_OWNB_Cursor PV_OWN_Link

theorem sink (q : Cursor) (v : Link) (actual : PV_OWN_Bytes.Bytes) :
 PV_OWNB_Prefix.values (PV_OWNB_ActualSink.sink q v actual)=PV_OWNB_Prefix.values q++[v] := by
 unfold PV_OWNB_Prefix.values PV_OWNB_ActualSink.sink
 dsimp only
 rw [List.range_succ,List.map_append]
 simp only [List.map_cons,List.map_nil,ite_true]
 congr 1
 apply List.map_congr_left
 intro i hi
 have small:i<q.written := List.mem_range.mp hi
 have ne:i≠q.written := by omega
 simp [ne]
#print axioms sink
end R1Z.PV_OWNB_ActualPrefix
