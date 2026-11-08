import NNV_PreparedPorts
import NFW_PreparedPort
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNV_PreparedStateTransport
open Aeneas Aeneas.Std Result AspisR1CurrentCaller
open AspisR1PublicPreparation

theorem field (x : aspis_core.field.WideExact) :
 Tx1Q_Carriers.e (InstalledPreparation.currentE x) = NFW_PreparedPort.e x := rfl

theorem prepared (p : AspisR1PublicPreparation.verifier.Prepared) :
 Tx1Q_Carriers.prepared (InstalledPreparation.currentPrepared p) = NFW_PreparedPort.prepared p := by
 cases p with
 | mk variant roots gamma kappa alpha rho queries semantic_alpha z claim state =>
  cases variant <;>
   simp only [Tx1Q_Carriers.prepared,InstalledPreparation.currentPrepared,
    NFW_PreparedPort.prepared,Tx1Q_Carriers.arr,AspisR1ClaimPreparedBridge.mapArray,
    NFW_PreparedPort.map,List.map_map,Function.comp_def]
  all_goals rfl

theorem scratch (g : LIB_VCarriers.E29) :
 Tx1Q_Carriers.arr Tx1Q_Carriers.e
  (AspisR1ClaimPreparedBridge.mapArray InstalledPreparation.currentE g) =
 NFW_PreparedPort.map NFW_PreparedPort.e g := by
 apply Subtype.ext
 simp only [Tx1Q_Carriers.arr,AspisR1ClaimPreparedBridge.mapArray,NFW_PreparedPort.map,
  List.map_map,Function.comp_def,field]
#print axioms field
#print axioms prepared
#print axioms scratch
end AspisR1.NNV_PreparedStateTransport
end
