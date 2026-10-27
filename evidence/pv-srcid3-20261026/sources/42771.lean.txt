import R1Z.PV_Src_RootCell00
import R1Z.PV_Src_RootCell01
import R1Z.PV_Src_RootCell02
import R1Z.PV_Src_RootCell03
import R1Z.PV_Src_RootCell04
import R1Z.PV_Src_RootCell05
import R1Z.PV_Src_RootCell06
import R1Z.PV_Src_RootCell07
import R1Z.PV_Src_RootCell08
import R1Z.PV_Src_RootCell09
import R1Z.PV_Src_RootCell10
import R1Z.PV_Src_RootCell11
import R1Z.PV_Src_RootCell12
import R1Z.PV_Src_RootCell13
import R1Z.PV_Src_RootCell14
import R1Z.PV_Src_RootCell15
import R1Z.PV_Src_RootCell16
import R1Z.PV_Src_RootCell17
import R1Z.PV_Src_RootCell18
import R1Z.PV_Src_RootCell19
import R1Z.PV_Src_RootCell20
set_option autoImplicit false
namespace R1Z.PV_Src_RootParents
open Aeneas Aeneas.Std Result BuilderForestAdmissionPort

theorem source (l : Fin 20) : pool_v1.format.pool_v1_tree_parent
    (sourceExternalLinear := PV_Src_ExternalReference.dictionary)
    PV_Src_CanonicalRoots.table.val[l.val]! PV_Src_CanonicalRoots.table.val[l.val]! =
      ok PV_Src_CanonicalRoots.table.val[l.val+1]! := by
  fin_cases l
  · exact PV_Src_RootCell01.source
  · exact PV_Src_RootCell02.source
  · exact PV_Src_RootCell03.source
  · exact PV_Src_RootCell04.source
  · exact PV_Src_RootCell05.source
  · exact PV_Src_RootCell06.source
  · exact PV_Src_RootCell07.source
  · exact PV_Src_RootCell08.source
  · exact PV_Src_RootCell09.source
  · exact PV_Src_RootCell10.source
  · exact PV_Src_RootCell11.source
  · exact PV_Src_RootCell12.source
  · exact PV_Src_RootCell13.source
  · exact PV_Src_RootCell14.source
  · exact PV_Src_RootCell15.source
  · exact PV_Src_RootCell16.source
  · exact PV_Src_RootCell17.source
  · exact PV_Src_RootCell18.source
  · exact PV_Src_RootCell19.source
  · exact PV_Src_RootCell20.source

#print axioms source
end R1Z.PV_Src_RootParents
