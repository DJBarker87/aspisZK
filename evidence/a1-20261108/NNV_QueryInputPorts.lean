import NNV_CurrentQuerySource
import NNV_CurrentGeometry
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNV_QueryInputPorts
open Aeneas Aeneas.Std Result

theorem accumulator (a : LIB_VCarriers.Acc) :
 Tx1Q_Carriers.accumulator (Tx1Q_Carriers.unAccumulator (LIBC_VStateCarriers.toAcc a)) =
 LIBC_VStateCarriers.toAcc a := Tx1Q_Carriers.accumulator_roundtrip _

theorem pending (p : LIB_VCarriers.Weights) :
 Tx1Q_Carriers.pending (Tx1Q_Carriers.unPending p) = p := Tx1Q_Carriers.pending_roundtrip _

theorem geometry (g : LIB_VCarriers.Geo) :
 Tx1Q_Carriers.geometry (Tx1Q_PrefixInstall.unGeometry g) = g := by cases g; rfl
#print axioms accumulator
#print axioms pending
#print axioms geometry
end AspisR1.NNV_QueryInputPorts
end
