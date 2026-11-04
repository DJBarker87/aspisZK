import PV_RJ4IDB_NativeChannels
set_option autoImplicit false
namespace PV_RJ4IDB
/-- Explicit composition of the native visible channels. Bytes and event order
are retained; no file success, suppressed error, zero time or empty prefix is
chosen. Native acquisition of each channel remains a named owning-line input. -/
def nativeObservation {A : Type} (t : NativeTrace A) : Observation A :=
 ⟨t.events.map translateEvent,t.terminal,nativeFiles t.events,nativeJSON t.events,
 nativeStdout t.events,nativeDiag2 t.events,nativeDiag3 t.events,nativeCounts t.events,
 nativeTimes t.events,nativeOracle t.events,nativeRejections t.events,nativeSide t.events⟩

theorem native_factorization {A : Type} (t : NativeTrace A) :
 nativeObservation t = decoder (modelTrace t) := by
 simp only [nativeObservation,decoder,modelTrace,nativeFiles_translation,
 nativeJSON_translation,nativeStdout_translation,nativeDiag2_translation,
 nativeDiag3_translation,nativeCounts_translation,nativeTimes_translation,
 nativeOracle_translation,nativeRejections_translation,nativeSide_translation]

theorem success_factorization {A : Type} (es : List NativeEvent) (value : A) :
 nativeObservation ⟨es,.success value⟩ = decoder (modelTrace ⟨es,.success value⟩) :=
 native_factorization _

theorem failure_factorization (es : List NativeEvent) (error : Bytes) :
 nativeObservation (⟨es,.failure error⟩ : NativeTrace Unit) =
 decoder (modelTrace ⟨es,.failure error⟩) := native_factorization _

theorem divergence_factorization (es : List NativeEvent) :
 nativeObservation (⟨es,.diverge⟩ : NativeTrace Unit) =
 decoder (modelTrace ⟨es,.diverge⟩) := native_factorization _

theorem panic_factorization (es : List NativeEvent) (p : PV_DIAG3.Panic) :
 nativeObservation (⟨es,.panic p⟩ : NativeTrace Unit) =
 decoder (modelTrace ⟨es,.panic p⟩) := native_factorization _

theorem abort_factorization (es : List NativeEvent) (c : PV_DIAG3.Crash) :
 nativeObservation (⟨es,.abort c⟩ : NativeTrace Unit) =
 decoder (modelTrace ⟨es,.abort c⟩) := native_factorization _

/-- This covers every native prefix family, including each emitting prefix of
an infinite run. The index set is arbitrary and need not be finite. -/
theorem all_prefixes {I A : Type} (family : I → NativeTrace A) :
 ∀ i, nativeObservation (family i) = decoder (modelTrace (family i)) :=
 fun i => native_factorization (family i)
#print axioms native_factorization
#print axioms success_factorization
#print axioms failure_factorization
#print axioms divergence_factorization
#print axioms panic_factorization
#print axioms abort_factorization
#print axioms all_prefixes
end PV_RJ4IDB
