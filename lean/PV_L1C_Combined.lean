import PV_L1C_Order
import PV_L1C_TimingLaw
set_option autoImplicit false
noncomputable section
namespace PV_L1C
open PV_RJ4IDB R0Z

/-- Conditional MODEL composition on the SAME original sample carrier.
This does not instantiate the native event producers, clock law, or simE.
The hypothesis is explicitly unproved for the deployed program. -/
theorem combined_observer_law {S T A : Type} [Fintype S] [Fintype T]
 (real : S → NativeTrace A) (sim : T → NativeTrace A)
 (timing_and_context : JointTimingLaw real sim) :
 EqualLaws (fun s => nativeObservation (real s))
  (fun t => decoder (modelTrace (sim t))) := by
 have full := (full_law_iff_timing_law real sim).mpr timing_and_context
 have observed := law_map real sim nativeObservation full
 simpa only [native_factorization] using observed

/-- The four EXACT requested input types, on one index family. This is a
statement of remaining work, with NO instance and no added trust field. -/
def PendingNativeInputs {I A : Type}
 (actualCount : I → List Nat × List Nat) (actualTime : I → List Bytes)
 (actualOracle actualSide : I → List (Bytes × Bytes))
 (native : I → NativeTrace A) : Prop :=
 OpenInputs.L1_COUNT_TRACE actualCount native ∧
 OpenInputs.L1_TIME_TRACE actualTime native ∧
 OpenInputs.L1_ORACLE_PREFIX actualOracle native ∧
 OpenInputs.L1_RETAINED_SIDECHANNELS actualSide native

#print axioms combined_observer_law
end PV_L1C
