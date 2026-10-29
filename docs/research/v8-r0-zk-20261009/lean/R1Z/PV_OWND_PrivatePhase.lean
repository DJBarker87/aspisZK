import R1Z.PV_OWND_Private00
import R1Z.PV_OWND_Private01
import R1Z.PV_OWND_Private02
import R1Z.PV_OWND_Private03
import R1Z.PV_OWND_Private04
import R1Z.PV_OWND_Private05
import R1Z.PV_OWND_Private06
import R1Z.PV_OWND_Private07
import R1Z.PV_OWND_Private08
import R1Z.PV_OWND_Private09
import R1Z.PV_OWND_Private10
import R1Z.PV_OWND_Private11
import R1Z.PV_OWND_Private12
import R1Z.PV_OWND_Private13
import R1Z.PV_OWND_Private14
import R1Z.PV_OWND_Private15
import R1Z.PV_OWND_Private16
import R1Z.PV_OWND_Private17
import R1Z.PV_OWND_Private18
import R1Z.PV_OWND_Private19
import R1Z.PV_OWND_Private20
set_option autoImplicit false
namespace R1Z.PV_OWND_PrivatePhase
open PV_OWND_LegacySource PV_OWN_Link
def values : List Link := PV_OWND_Private00.values ++ PV_OWND_Private01.values ++ PV_OWND_Private02.values ++ PV_OWND_Private03.values ++ PV_OWND_Private04.values ++ PV_OWND_Private05.values ++ PV_OWND_Private06.values ++ PV_OWND_Private07.values ++ PV_OWND_Private08.values ++ PV_OWND_Private09.values ++ PV_OWND_Private10.values ++ PV_OWND_Private11.values ++ PV_OWND_Private12.values ++ PV_OWND_Private13.values ++ PV_OWND_Private14.values ++ PV_OWND_Private15.values ++ PV_OWND_Private16.values ++ PV_OWND_Private17.values ++ PV_OWND_Private18.values ++ PV_OWND_Private19.values ++ PV_OWND_Private20.values
theorem source : privateLinks=values := by
 unfold privateLinks
 have range : List.range 21=[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20] := rfl
 rw [range]
 simp only [List.flatMap_cons,List.flatMap_nil,List.append_nil,PV_OWND_Private00.source,PV_OWND_Private01.source,PV_OWND_Private02.source,PV_OWND_Private03.source,PV_OWND_Private04.source,PV_OWND_Private05.source,PV_OWND_Private06.source,PV_OWND_Private07.source,PV_OWND_Private08.source,PV_OWND_Private09.source,PV_OWND_Private10.source,PV_OWND_Private11.source,PV_OWND_Private12.source,PV_OWND_Private13.source,PV_OWND_Private14.source,PV_OWND_Private15.source,PV_OWND_Private16.source,PV_OWND_Private17.source,PV_OWND_Private18.source,PV_OWND_Private19.source,PV_OWND_Private20.source]
 rfl

theorem count : values.length=63 := by
 simp only [values,List.length_append,PV_OWND_Private00.count,PV_OWND_Private01.count,PV_OWND_Private02.count,PV_OWND_Private03.count,PV_OWND_Private04.count,PV_OWND_Private05.count,PV_OWND_Private06.count,PV_OWND_Private07.count,PV_OWND_Private08.count,PV_OWND_Private09.count,PV_OWND_Private10.count,PV_OWND_Private11.count,PV_OWND_Private12.count,PV_OWND_Private13.count,PV_OWND_Private14.count,PV_OWND_Private15.count,PV_OWND_Private16.count,PV_OWND_Private17.count,PV_OWND_Private18.count,PV_OWND_Private19.count,PV_OWND_Private20.count]
#print axioms source
#print axioms count
attribute [local irreducible] values
end R1Z.PV_OWND_PrivatePhase
