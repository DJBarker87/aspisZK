import PV_LIB_Observation
import PV_LIB_Array11View
import PV_LIB_Array12View
import PV_LIB_Array15View
import PV_LIB_Array23View
set_option autoImplicit false
noncomputable section
namespace PV_LIB_ArrayInstances
open PV_EVHB_OwnerMachine PV_STX2_Syntax

def model12 {E : Type} (x : PV_LIB_Array12View.Input E) :=
  PV_LIB.observe (PV_LIB_Array12View.internalModel x)
def law12 {E : Type} (x : PV_LIB_Array12View.Input E)
    (out : PV_LIB.MachineObservation OWNER E) : Prop := out = model12 x
theorem installed12 {E : Type} (x : PV_LIB_Array12View.Input E)
    (pre : PV_FN_SLICE_f12.Pre x) :
    law12 x (PV_LIB.observe (PV_LIB_Array12View.internalActual x)) := by
  change PV_LIB.observe (PV_LIB_Array12View.internalActual x) = PV_LIB.observe (PV_LIB_Array12View.internalModel x)
  have h := PV_LIB_Array12View.installed x pre
  change PV_LIB.view (PV_LIB_Array12View.internalActual x) = PV_LIB.view (PV_LIB_Array12View.internalModel x) at h
  simpa only [PV_LIB.observe_view] using congrArg PV_LIB.observe h
#print axioms installed12

def model15 {E : Type} (x : PV_LIB_Array15View.Input E) (k : Data) :=
  PV_LIB.observe (PV_LIB_Array15View.internalModel x k)
def law15 {E : Type} (x : PV_LIB_Array15View.Input E) (k : Data)
    (out : PV_LIB.MachineObservation OWNER E) : Prop := out = model15 x k
theorem installed15 {E : Type} (x : PV_LIB_Array15View.Input E) (k : Data)
    (pre : PV_FN_SLICE_f15.Pre x k) :
    law15 x k (PV_LIB.observe (PV_LIB_Array15View.internalActual x)) := by
  change PV_LIB.observe (PV_LIB_Array15View.internalActual x) = PV_LIB.observe (PV_LIB_Array15View.internalModel x k)
  have h := PV_LIB_Array15View.installed x k pre
  change PV_LIB.view (PV_LIB_Array15View.internalActual x) = PV_LIB.view (PV_LIB_Array15View.internalModel x k) at h
  simpa only [PV_LIB.observe_view] using congrArg PV_LIB.observe h
#print axioms installed15

def model23 {E : Type} (x : PV_LIB_Array23View.Input E) :=
  PV_LIB.observe (PV_LIB_Array23View.internalModel x)
def law23 {E : Type} (x : PV_LIB_Array23View.Input E)
    (out : PV_LIB.MachineObservation OWNER E) : Prop := out = model23 x
theorem installed23 {E : Type} (x : PV_LIB_Array23View.Input E)
    (pre : PV_FN_SLICE_f23.Pre x) :
    law23 x (PV_LIB.observe (PV_LIB_Array23View.internalActual x)) := by
  change PV_LIB.observe (PV_LIB_Array23View.internalActual x) = PV_LIB.observe (PV_LIB_Array23View.internalModel x)
  have h := PV_LIB_Array23View.installed x pre
  change PV_LIB.view (PV_LIB_Array23View.internalActual x) = PV_LIB.view (PV_LIB_Array23View.internalModel x) at h
  simpa only [PV_LIB.observe_view] using congrArg PV_LIB.observe h
#print axioms installed23
end PV_LIB_ArrayInstances
