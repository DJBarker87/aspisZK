import PV_L1E_CountSkeleton
import R1Z.SideChannelL1AttemptRecord
set_option autoImplicit false
namespace PV_L1E_OriginalCountSkeleton
open PV_RJ4IDB
open R1Z.SideChannelL1AttemptRecord (Owner Run run)
open PV_L1E_CountSkeleton
variable {I A S P : Type}

/-- The adapter is an independent source-world operation, not a native decoder.
It must retain client operations and terminal status. D163 alone does not
construct this adapter, nor the interrupted-prefix extension it requires. -/
def PV_L1E_Link_OriginalRetry (bodyWorld : I → Trace A)
    (owner : I → Owner S P) (initial : I → S) (fuel index : I → Nat)
    (adapt : I → Run P × S → Trace A) : Prop :=
  ∀ i, bodyWorld i = adapt i (run (owner i) (fuel i) (index i) (initial i))

/-- Same owner, state, fuel, index and source-world adapter in the native join.
The full original-to-simE distributional coupling remains additional work:
this exact decoder input states pathwise acquisition, not a privacy bound. -/
def PV_L1E_Link_NativeD163 (native : I → NativeTrace A)
    (owner : I → Owner S P) (initial : I → S) (fuel index : I → Nat)
    (adapt : I → Run P × S → Trace A) : Prop :=
  ∀ i, adapt i (run (owner i) (fuel i) (index i) (initial i)) = modelTrace (native i)

theorem original_count_trace (actualCount : I → List Nat × List Nat)
    (native : I → NativeTrace A) (sourceWorld bodyWorld : I → Trace A)
    (owner : I → Owner S P) (initial : I → S) (fuel index : I → Nat)
    (adapt : I → Run P × S → Trace A)
    (acquisition : PV_L1E_Link_CountAcquisition actualCount sourceWorld)
    (body : PV_L1E_Link_BodyWrapper sourceWorld bodyWorld)
    (retry : PV_L1E_Link_OriginalRetry bodyWorld owner initial fuel index adapt)
    (coupling : PV_L1E_Link_NativeD163 native owner initial fuel index adapt) :
    PV_RJ4IDB.OpenInputs.L1_COUNT_TRACE actualCount native :=
  count_trace actualCount native sourceWorld bodyWorld
    (fun i => adapt i (run (owner i) (fuel i) (index i) (initial i)))
    acquisition body retry coupling
#print original_count_trace
#print axioms original_count_trace
end PV_L1E_OriginalCountSkeleton
