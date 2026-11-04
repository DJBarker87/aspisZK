import PV_RJ4IDB_Publication
import PV_RJ4IDB_NativeFactor
/-! Exact typed OPEN native producer inputs. These Props have no instances and
are not hypotheses of native_factorization or any theorem claiming deployed
privacy. I ranges over all admitted paths/prefixes, with no finiteness or
successful-return restriction. Owners are listed in OPEN-INPUTS.md. -/
set_option autoImplicit false
namespace PV_RJ4IDB.OpenInputs
variable {I A : Type}

def RUNJOIN_PUBLISH_COMPACT (actual : I → Option Bytes)
 (published : I → Option PublicationInput) : Prop :=
 ∀ i, actual i = (published i).map PublicationInput.publish_compact

def RUNJOIN_STATEMENT_BYTES (actual : I → Option Bytes)
 (published : I → Option PublicationInput) : Prop :=
 ∀ i, actual i = (published i).map PublicationInput.statement

def DIAG_FILE_TRACE (actual : I → List FileOp) (native : I → NativeTrace A) : Prop :=
 ∀ i, actual i = nativeFiles (native i).events

def DIAG_JSON_STDOUT_TRACE (actual : I → List Bytes × List (Bytes × Bytes))
 (native : I → NativeTrace A) : Prop :=
 ∀ i, actual i = (nativeJSON (native i).events,nativeStdout (native i).events)

def DIAG_ERROR_STDERR_TRACE
 (actual : I → List PV_DIAG2.Effect × List PV_DIAG3.Event)
 (native : I → NativeTrace A) : Prop :=
 ∀ i, actual i = (nativeDiag2 (native i).events,nativeDiag3 (native i).events)

def L1_COUNT_TRACE (actual : I → List Nat × List Nat)
 (native : I → NativeTrace A) : Prop :=
 ∀ i, actual i = (nativeCounts (native i).events,nativeRejections (native i).events)

def L1_TIME_TRACE (actual : I → List Bytes) (native : I → NativeTrace A) : Prop :=
 ∀ i, actual i = nativeTimes (native i).events

def L1_ORACLE_PREFIX (actual : I → List (Bytes × Bytes))
 (native : I → NativeTrace A) : Prop :=
 ∀ i, actual i = nativeOracle (native i).events

def L1_RETAINED_SIDECHANNELS (actual : I → List (Bytes × Bytes))
 (native : I → NativeTrace A) : Prop :=
 ∀ i, actual i = nativeSide (native i).events

#print axioms RUNJOIN_PUBLISH_COMPACT
#print axioms RUNJOIN_STATEMENT_BYTES
#print axioms DIAG_FILE_TRACE
#print axioms DIAG_JSON_STDOUT_TRACE
#print axioms DIAG_ERROR_STDERR_TRACE
#print axioms L1_COUNT_TRACE
#print axioms L1_TIME_TRACE
#print axioms L1_ORACLE_PREFIX
#print axioms L1_RETAINED_SIDECHANNELS
end PV_RJ4IDB.OpenInputs
