import S1QueryModelContinuationV1
import S1ClosedPreparationCausalProgramV1
set_option autoImplicit false
noncomputable section
namespace AspisR1PublicPreparation.PreparedHashCode
open Aeneas Aeneas.Std Result

def pairedPreparationEffects (B : PreparedScratchModel.Boundaries) (Q : QueriesModel.Boundaries) :
    PreparedSourceEffects.Effects Code :=
  {preparationEffects B Q with queries := PreparedQueryMaterialize.queriesWithPairs Q}

private theorem updateQueries_self (e : PreparedSourceEffects.Effects Code) :
    {e with queries := e.queries}=e := by cases e; rfl

/-- This is equality of the concrete child definitions, not a new field
requiring the caller to assume a desired query/output/log correspondence. -/
theorem pairedPreparationEffects_eq (B : PreparedScratchModel.Boundaries) (Q : QueriesModel.Boundaries) :
    pairedPreparationEffects B Q=preparationEffects B Q := by
  have law : @PreparedSourceEffects.Effects.queries (preparationEffects B Q)=
      @PreparedQueryMaterialize.queriesWithPairs Q := by
    funext H D self row payload
    exact PreparedQueryMaterialize.queries_code_eq_pairs Q D self row payload
  unfold pairedPreparationEffects
  rw [← law]

theorem preparation_code_eq_pairs (B : PreparedScratchModel.Boundaries) (Q : QueriesModel.Boundaries)
    {H : Type} (D : aspis_core.Digest32 H) (sem : r1_semantic.Verified H)
    (view : verifier.View) (hash : H) (scratch : Array aspis_core.field.WideExact 29#usize) :
    PreparedSourceEffects.prepare (preparationEffects B Q) D sem view hash scratch=
      PreparedSourceEffects.prepare (pairedPreparationEffects B Q) D sem view hash scratch := by
  rw [pairedPreparationEffects_eq]

#print axioms pairedPreparationEffects_eq
#print axioms preparation_code_eq_pairs
end AspisR1PublicPreparation.PreparedHashCode
namespace AspisR1CurrentCaller.BorrowedClaimPrepared
open Aeneas Aeneas.Std Result
open AspisR1CurrentCaller AspisR1ClaimPreparedBridge
open AspisR1PublicPreparation.PreparedHashCode
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw
open S4SolanaDigestWrapperP3BindingV1

def pairedClosedPreparationCode {H : Type} (D : aspis_core.digest.Digest32 H)
    (sem : r1_semantic.Verified H) (view : verifier.View) (hash : H)
    (scratch : Array aspis_core.field.wide_exact.WideExact 29#usize) :
    Code (core.result.Result verifier.Prepared verifier.Error ×
      Array aspis_core.field.wide_exact.WideExact 29#usize) := do
  let (r,g) ← AspisR1PublicPreparation.PreparedSourceEffects.prepare
    (pairedPreparationEffects closedHashBoundaries closedHashQueries)
    (InstalledPreparation.retainedDigest D) (InstalledPreparation.retainedSem sem)
    (InstalledPreparation.retainedView view) hash (mapArray InstalledPreparation.retainedE scratch)
  pure ((match r with
    | .Ok x => .Ok (InstalledPreparation.currentPrepared x)
    | .Err e => .Err (InstalledPreparation.currentError e)),mapArray InstalledPreparation.currentE g)

theorem closedPreparationCode_eq_pairs {H : Type} (D : aspis_core.digest.Digest32 H)
    (sem : r1_semantic.Verified H) (view : verifier.View) (hash : H)
    (scratch : Array aspis_core.field.wide_exact.WideExact 29#usize) :
    closedPreparationCode D sem view hash scratch=pairedClosedPreparationCode D sem view hash scratch := by
  unfold closedPreparationCode pairedClosedPreparationCode
  rw [pairedPreparationEffects_eq]

def pairedCausalPreparationProgram (sem : r1_semantic.Verified SolanaDigest)
    (view : verifier.View) (hash : SolanaDigest)
    (scratch : Array aspis_core.field.wide_exact.WideExact 29#usize) :
    Program Bytes State (Result (core.result.Result verifier.Prepared verifier.Error ×
      Array aspis_core.field.wide_exact.WideExact 29#usize)) :=
  oracleProgram (pairedClosedPreparationCode
    (p3CallerDigest (fun _ => Array.repeat 32#usize 0#u8)) sem view hash scratch)

theorem pairedCausalPreparationProgram_eq (sem : r1_semantic.Verified SolanaDigest)
    (view : verifier.View) (hash : SolanaDigest)
    (scratch : Array aspis_core.field.wide_exact.WideExact 29#usize) :
    pairedCausalPreparationProgram sem view hash scratch=causalPreparationProgram sem view hash scratch := by
  unfold pairedCausalPreparationProgram causalPreparationProgram
  rw [closedPreparationCode_eq_pairs]

#print axioms closedPreparationCode_eq_pairs
#print axioms pairedCausalPreparationProgram_eq
end AspisR1CurrentCaller.BorrowedClaimPrepared
