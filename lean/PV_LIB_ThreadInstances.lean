import PV_LIB_Observation
import PV_LIB_Thread315
import PV_LIB_Thread218
import PV_LIB_Thread164
import PV_LIB_Arc222
import PV_LIB_Arc126
set_option autoImplicit false
noncomputable section
namespace PV_LIB_ThreadInstances
open PV_EVHB_OwnerMachine PV_STX2_Syntax PV_STX2_Store

def model315 {E : Type} (x : PV_LIB_Thread315.Input E) := PV_LIB.observe (PV_LIB_Thread315.internalModel x)
def law315 {E : Type} (x : PV_LIB_Thread315.Input E)
    (out : PV_LIB.MachineObservation OWNER E) : Prop := out = model315 x
theorem installed315 {E : Type} (x : PV_LIB_Thread315.Input E) (pre : PV_FN_THREAD_f315.Pre x) :
    law315 x (PV_LIB.observe (PV_LIB_Thread315.internalActual x)) := by
  change PV_LIB.observe (PV_LIB_Thread315.internalActual x) = PV_LIB.observe (PV_LIB_Thread315.internalModel x)
  have h := PV_LIB_Thread315.installed x pre
  change PV_LIB.view (PV_LIB_Thread315.internalActual x) = PV_LIB.view (PV_LIB_Thread315.internalModel x) at h
  simpa only [PV_LIB.observe_view] using congrArg PV_LIB.observe h
#print axioms installed315

def model218 {E : Type} (x : PV_LIB_Thread218.Input E) := PV_LIB.observe (PV_LIB_Thread218.internalModel x)
def law218 {E : Type} (x : PV_LIB_Thread218.Input E)
    (out : PV_LIB.MachineObservation OWNER E) : Prop := out = model218 x
theorem installed218 {E : Type} (x : PV_LIB_Thread218.Input E) (pre : PV_FN_THREAD_f218.Pre x) :
    law218 x (PV_LIB.observe (PV_LIB_Thread218.internalActual x)) := by
  change PV_LIB.observe (PV_LIB_Thread218.internalActual x) = PV_LIB.observe (PV_LIB_Thread218.internalModel x)
  have h := PV_LIB_Thread218.installed x pre
  change PV_LIB.view (PV_LIB_Thread218.internalActual x) = PV_LIB.view (PV_LIB_Thread218.internalModel x) at h
  simpa only [PV_LIB.observe_view] using congrArg PV_LIB.observe h
#print axioms installed218

def model222 {E : Type} (x : PV_LIB_Arc222.Input E) (H : PV_FN_THREAD_f222.Backend E) (p : Address) :=
  PV_LIB.observe (PV_LIB_Arc222.internalModel x H p)
def law222 {E : Type} (x : PV_LIB_Arc222.Input E) (H : PV_FN_THREAD_f222.Backend E) (p : Address)
    (out : PV_LIB.MachineObservation OWNER E) : Prop := out = model222 x H p
theorem installed222 {E : Type} (x : PV_LIB_Arc222.Input E) (H : PV_FN_THREAD_f222.Backend E) (p : Address)
    (pre : PV_FN_THREAD_f222.Pre x p) :
    ∃ out, PV_FN_THREAD_f222.Reached x H out ∧ law222 x H p (PV_LIB.observe out) :=
  ⟨PV_LIB_Arc222.internalModel x H p,PV_LIB_Arc222.internal_reached x H p pre,rfl⟩
#print axioms installed222

def model126 {E : Type} (x : PV_LIB_Arc126.Input E) (H : PV_FN_THREAD_f126.Backend E) (arc p : Address) :=
  PV_LIB.observe (PV_LIB_Arc126.internalModel x H arc p)
def law126 {E : Type} (x : PV_LIB_Arc126.Input E) (H : PV_FN_THREAD_f126.Backend E) (arc p : Address)
    (out : PV_LIB.MachineObservation OWNER E) : Prop := out = model126 x H arc p
theorem installed126 {E : Type} (x : PV_LIB_Arc126.Input E) (H : PV_FN_THREAD_f126.Backend E) (arc p : Address)
    (pre : PV_FN_THREAD_f126.Pre x arc p) :
    ∃ out, PV_FN_THREAD_f126.Reached x H arc out ∧ law126 x H arc p (PV_LIB.observe out) :=
  ⟨PV_LIB_Arc126.internalModel x H arc p,PV_LIB_Arc126.internal_reached x H arc p pre,rfl⟩
#print axioms installed126
end PV_LIB_ThreadInstances
