import NNU_QueryFieldQM
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNU_QueryFieldCarriers
open Aeneas Aeneas.Std Result AspisR1Stage2
abbrev K := aspis_core.field.QM31

theorem addQ (x y : K) :
 (do let z ← AspisR1CurrentWide.field.QM31.add (SAQ_WideABI.toQ x) (SAQ_WideABI.toQ y)
     ok (SAQ_WideABI.fromQ z)) =
 (do let z ← AspisR1SelectedMaskProbe.field.QM31.add (NBO_FieldPorts.toQ x) (NBO_FieldPorts.toQ y)
     ok (NBO_FieldPorts.fromQ z)) := by
 have h := congrArg (fun r : Result AspisR1SelectedMaskProbe.field.QM31 =>
   do let z ← r; ok (NBO_FieldPorts.fromQ z))
  (NNU_QueryFieldQM.qm_add_same (SAQ_WideABI.toQ x) (SAQ_WideABI.toQ y))
 simpa only [bind_assoc_eq,bind_tc_ok,NNU_QueryFieldBase.toQM,NNU_QueryFieldBase.toCM,
  NBO_FieldPorts.fromQ,SAQ_WideABI.fromQ] using h

theorem mulQ (x y : K) : SAQ_Arithmetic.mulK x y = NBO_FieldSemantics.power x y := by
 unfold SAQ_Arithmetic.mulK NBO_FieldSemantics.power
 have h := congrArg (fun r : Result AspisR1SelectedMaskProbe.field.QM31 =>
   do let z ← r; ok (NBO_FieldPorts.fromQ z))
  (NNU_QueryFieldQM.qm_mul_same (SAQ_WideABI.toQ x) (SAQ_WideABI.toQ y))
 simpa only [bind_assoc_eq,bind_tc_ok,NNU_QueryFieldBase.toQM,NNU_QueryFieldBase.toCM,
  NBO_FieldPorts.fromQ,SAQ_WideABI.fromQ] using h
#print axioms addQ
#print axioms mulQ
end AspisR1.NNU_QueryFieldCarriers
end
