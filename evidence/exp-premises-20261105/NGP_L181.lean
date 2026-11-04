import NGK_COMBINED_IMPORT

/-! Exact transport interfaces. These definitions assert no physical realization
and introduce no random-oracle distribution or new runtime trust. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.NGP_L181
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps

/-- A terminal may be pure rejection, fail or divergence. Each attempted
syscall retains its full parts and returned Result, including unsuccessful calls. -/
structure Observation (A : Type) where
  result : Result A
  attempted : SdkC_Source.Log

/-- Physical-to-source transport is a producer obligation on a single run.
It includes ALL attempted occurrences, never a deduplicated set. -/
def NativeAssociation {A : Type} (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (code : CheckpointBytes5Effect.Code A) (observed : Observation A) : Prop :=
  (observed.result, observed.attempted) = SdkC_Source.run hashv code []

/-- General partial-syscall form: the real attempted addresses form an exact
prefix of the ideal event sequence, including the unsuccessful call itself.
The omitted suffix remains in the ideal experiment; it is not silently erased. -/
def Prefix_statement {A : Type} (H : Bytes → State)
    (code : CheckpointBytes5Effect.Code A) (observed : Observation A) : Prop :=
  ∃ suffix : List Bytes,
    (eval H (SdkC_Oracle.program code)).1.map Prod.fst =
      RPx_AttemptPrefix.addresses observed.attempted ++ suffix

/-- Exact form when all attempted syscalls return; pure verifier rejection is
allowed. P1/RuntimeSyscall supply agreement, not syscall totality. -/
def Exact_statement {A : Type} (H : Bytes → State)
    (code : CheckpointBytes5Effect.Code A) (observed : Observation A) : Prop :=
  observed.result = (eval H (SdkC_Oracle.program code)).2 ∧
  SdkC_Source.readLog observed.attempted = (eval H (SdkC_Oracle.program code)).1 ∧
  RPx_AttemptPrefix.addresses observed.attempted =
    (eval H (SdkC_Oracle.program code)).1.map Prod.fst

/-- L181 is universal over the actual observed family; callers must construct
native association from frozen execution. Equality of query-loop Results alone
is insufficient. Exact transport is conditional ONLY on returned-call coverage;
all other outcomes retain the chronological prefix obligation. -/
def L181_statement {A : Type}
    (actual : (Bytes → State) → Observation A)
    (code : CheckpointBytes5Effect.Code A) : Prop :=
  ∀ H, Prefix_statement H code (actual H) ∧
    (ARR_ReturnCoverage.ReturnsOnly (actual H).attempted →
      Exact_statement H code (actual H))

/-- This is the model-side final probability obligation already used by the
headline. Instantiating its runtime with a physical execution is separate. -/
def Mass_statement (runtime : F3T_Runtime.Runtime) (Q : Nat) : Prop :=
  F3T_RuntimeBound.failureModel runtime ≤ F3T_Numeric.total Q

#print axioms NativeAssociation
#print axioms Prefix_statement
#print axioms Exact_statement
#print axioms L181_statement
#print axioms Mass_statement
end AspisR1.NGP_L181
