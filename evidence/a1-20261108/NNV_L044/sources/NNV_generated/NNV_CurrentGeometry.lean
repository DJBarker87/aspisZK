import NNV_GeometryOuter
import NNH_Run5bCurrentShape
import LIBC_Geometry
import NNH_Run5bReturnedGraph
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNV_CurrentGeometry
open Aeneas Aeneas.Std Result NNH_Run5bCurrentShape
variable (m : IDa_Deployed.Uninstalled NFN_NEW_GeometryDictionary.CE)
 (env : RSL.Env) (err : NFN_NEW_GeometryDictionary.CE) (r : NP6_StdModel.Reservation)

theorem slot (queries : Array U32 22#usize) (start stop : Usize) :
 (current m env err r).op19 queries start stop =
 Tx1Q_PrefixInstall.geometryBody (NNH_CorrectConfiguration.configuration m env err r).geometry queries start stop := rfl

theorem source (p : LIB_VCarriers.Prepared) (start stop : Usize) :
 (current m env err r).op19 p.queries start stop =
 Tx1Q_PrefixInstall.topResult Tx1Q_PrefixInstall.unGeometry
  (LIBC_Geometry.model (p,start.val,stop.val) env) := by
 rw [slot]
 unfold Tx1Q_PrefixInstall.geometryBody
 rw [NNV_GeometryOuter.stage]
 unfold LIBC_Geometry.model
 rw [LIBC_Usize.from_native start (by scalar_tac),LIBC_Usize.from_native stop (by scalar_tac)]

theorem returned (p : LIB_VCarriers.Prepared) (start stop : Usize) (geo : LIB_VCarriers.Geo)
 (called : LIB_VLib.geometryValue (p,start.val,stop.val) env = .ok geo) :
 (current m env err r).op19 p.queries start stop =
 .ok (.Ok (Tx1Q_PrefixInstall.unGeometry geo)) := by
 change LIBC_ResultGraph.value LIBC_Geometry.port (.error .Query)
  (LIBC_Geometry.model (p,start.val,stop.val) env) = .ok geo at called
 obtain ⟨reply,model,image⟩ := NNH_Run5bReturnedGraph.ok _ _ _ geo called
 cases reply with
 | Err e => cases image
 | Ok native =>
  have same : native = geo := Except.ok.inj image
  subst native
  rw [source,model]
  rfl
#print axioms slot
#print axioms source
#print axioms returned
end AspisR1.NNV_CurrentGeometry
end
