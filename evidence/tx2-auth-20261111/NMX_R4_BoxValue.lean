import NMX_R4_BoxEmitted
set_option autoImplicit false
noncomputable section
namespace NMX_R4_BoxValue
open Aeneas Aeneas.Std Result AdapterRw

theorem master (b : Slice U8) :
 NMX_R4_BoxEmitted.master NJQ_Canonical.master b = NKF_MasterBox.reference b := by
 unfold NMX_R4_BoxEmitted.master NKF_MasterBox.reference NKF_BoxModel.outer NJQ_Canonical.mapOuter
 cases h : NJQ_Canonical.master b with
 | fail e => rfl
 | div => rfl
 | ok r => cases r <;> rfl

theorem checkpoint (b : Slice U8) :
 NMX_R4_BoxEmitted.checkpoint NJQ_Canonical.checkpoint b = NKF_CheckpointBox.reference b := by
 unfold NMX_R4_BoxEmitted.checkpoint NKF_CheckpointBox.reference NKF_BoxModel.outer NJQ_Canonical.mapOuter
 cases h : NJQ_Canonical.checkpoint b with
 | fail e => rfl
 | div => rfl
 | ok r => cases r <;> rfl

#print axioms master
#print axioms checkpoint
end NMX_R4_BoxValue
end
