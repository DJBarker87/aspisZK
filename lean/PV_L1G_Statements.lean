import PV_L1G_BodyBind
import PV_L1G_CountPrefixes
import PV_L1G_OriginalRetry
import PV_L1G_SourcePublication
import PV_L1G_WorldCapture
import PV_L1G_WorldCongruence
import PV_L1G_WorldJoin
import PV_L1G_WorldPrefix
import PV_L1G_WorldReached
import PV_L1G_WorldRetry
import PV_L1G_WorldValidity
import PV_L1E_OriginalCountSkeleton
import PV_DIAG10_Operands
import PV_L1F_SourceRead
import PV_L1E_RetrySource
import PV_L1E_CallbackSafety
import PV_L1E_EntryOrder
set_option autoImplicit false
namespace PV_L1G_Statements
open PV_RJ4IDB PV_L1E_CountSkeleton PV_L1E_OriginalCountSkeleton
/-- Conditional composition only: all four frozen trace links and the frozen
joint diagnostic site law remain explicit. No concrete native instance or
original-to-simE coupling is manufactured by this conjunction. -/
theorem combined {I A S P C : Type} (actualCount : I → List Nat × List Nat)
 (native : I → NativeTrace A) (sourceWorld bodyWorld : I → Trace A)
 (owner : I → R1Z.SideChannelL1AttemptRecord.Owner S P)
 (initial : I → S) (fuel index : I → Nat)
 (adapt : I → R1Z.SideChannelL1AttemptRecord.Run P × S → Trace A)
 (context : I → C) (calls : I → PV_DIAG9.DiagnosticCall)
 (acquisition : PV_L1E_Link_CountAcquisition actualCount sourceWorld)
 (body : PV_L1E_Link_BodyWrapper sourceWorld bodyWorld)
 (retry : PV_L1E_Link_OriginalRetry bodyWorld owner initial fuel index adapt)
 (coupling : PV_L1E_Link_NativeD163 native owner initial fuel index adapt)
 (sites : PV_DIAG10.PV_DIAG10_Link_Sites context calls) :
 OpenInputs.L1_COUNT_TRACE actualCount native ∧
 PV_DIAG10.PV_DIAG10_Link_Sites context calls ∧
 ∀ i, nativeObservation (native i)=decoder (modelTrace (native i)) :=
 ⟨original_count_trace actualCount native sourceWorld bodyWorld owner initial fuel index adapt
   acquisition body retry coupling,sites,PV_RJ4IDB.all_prefixes native⟩
#print combined
#print axioms combined
end PV_L1G_Statements
