import R1Z.PV_OWND_Append00
import R1Z.PV_OWND_Append01
import R1Z.PV_OWND_Append02
import R1Z.PV_OWND_Append03
import R1Z.PV_OWND_Append04
import R1Z.PV_OWND_Append05
import R1Z.PV_OWND_Append06
import R1Z.PV_OWND_Append07
import R1Z.PV_OWND_Append08
import R1Z.PV_OWND_Append09
import R1Z.PV_OWND_Append10
import R1Z.PV_OWND_Append11
import R1Z.PV_OWND_Append12
import R1Z.PV_OWND_Append13
import R1Z.PV_OWND_Append14
import R1Z.PV_OWND_Append15
import R1Z.PV_OWND_Append16
import R1Z.PV_OWND_Append17
import R1Z.PV_OWND_Append18
import R1Z.PV_OWND_Append19
set_option autoImplicit false
namespace R1Z.PV_OWND_AppendPhase
open PV_OWND_LegacySource PV_OWN_Link
def values : List Link := PV_OWND_Append00.values ++ PV_OWND_Append01.values ++ PV_OWND_Append02.values ++ PV_OWND_Append03.values ++ PV_OWND_Append04.values ++ PV_OWND_Append05.values ++ PV_OWND_Append06.values ++ PV_OWND_Append07.values ++ PV_OWND_Append08.values ++ PV_OWND_Append09.values ++ PV_OWND_Append10.values ++ PV_OWND_Append11.values ++ PV_OWND_Append12.values ++ PV_OWND_Append13.values ++ PV_OWND_Append14.values ++ PV_OWND_Append15.values ++ PV_OWND_Append16.values ++ PV_OWND_Append17.values ++ PV_OWND_Append18.values ++ PV_OWND_Append19.values
theorem source : appendLinks=values := by
 unfold appendLinks
 have range : List.range 20=[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19] := rfl
 rw [range]
 simp only [List.flatMap_cons,List.flatMap_nil,List.append_nil,PV_OWND_Append00.source,PV_OWND_Append01.source,PV_OWND_Append02.source,PV_OWND_Append03.source,PV_OWND_Append04.source,PV_OWND_Append05.source,PV_OWND_Append06.source,PV_OWND_Append07.source,PV_OWND_Append08.source,PV_OWND_Append09.source,PV_OWND_Append10.source,PV_OWND_Append11.source,PV_OWND_Append12.source,PV_OWND_Append13.source,PV_OWND_Append14.source,PV_OWND_Append15.source,PV_OWND_Append16.source,PV_OWND_Append17.source,PV_OWND_Append18.source,PV_OWND_Append19.source]
 rfl

theorem count : values.length=40 := by
 simp only [values,List.length_append,PV_OWND_Append00.count,PV_OWND_Append01.count,PV_OWND_Append02.count,PV_OWND_Append03.count,PV_OWND_Append04.count,PV_OWND_Append05.count,PV_OWND_Append06.count,PV_OWND_Append07.count,PV_OWND_Append08.count,PV_OWND_Append09.count,PV_OWND_Append10.count,PV_OWND_Append11.count,PV_OWND_Append12.count,PV_OWND_Append13.count,PV_OWND_Append14.count,PV_OWND_Append15.count,PV_OWND_Append16.count,PV_OWND_Append17.count,PV_OWND_Append18.count,PV_OWND_Append19.count]
#print axioms source
#print axioms count
attribute [local irreducible] values
end R1Z.PV_OWND_AppendPhase
