import R1Z.PV_RunJoin_SelectedCoordinates32
import R1Z.PV_RunJoin_LedgerFrame32
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_LedgerCaller32
open Aeneas Aeneas.Std Result PV_RunJoin_HonestIdentification26
local instance : ProverRwRngCaller.NativeTypes := PV_RunJoin_CallerWorld.nativeTypes
local instance : ProverRwRngCaller.ErasureFns := ⟨fun _ value => .ok value,fun _ value => .ok value⟩
variable {N C : Type}

def publicTransition (base : ProverRwFull.ExternalTypes)
    (p : PV_RunJoin_NominalPublicData.TargetPublic base) :
    PV_RunJoin_NominalCompiledData.TargetTransition base := by
  letI : ProverRwFull.ExternalTypes := PDict_CodecDictionary.native base
  exact match p with | .Transfer _ t => t | .Withdrawal _ t => t

variable (base : ProverRwFull.ExternalTypes)
    (ops : PV_RunJoin_NativeSelectedInputs.LedgerState base N C →
      @ProverRwFull.ExternalFuns (PDict_CodecDictionary.native base))
    (hash : Slice (Slice U8) → Result (Array U8 32#usize))

theorem complete_public (i : PV_Src_NativeInput.Input)
    (s : PV_RunJoin_NativeSelectedInputs.LedgerState base N C) :
    letI : ProverRwFull.ExternalTypes := PDict_CodecDictionary.native base
    PV_RunJoin_NativePublicInverse32.unPublic base
      ((PV_RunJoin_NativeSelectedInputs.ledgerInputs base ops hash i).pub s) =
      PV_Src_NativeInput.publicInput i := by
  letI : ProverRwFull.ExternalTypes := PDict_CodecDictionary.native base
  exact PV_RunJoin_NativePublicInverse32.from_input_roundtrip base i
#print axioms complete_public

theorem complete_compiled (i : PV_Src_NativeInput.Input)
    (s : PV_RunJoin_NativeSelectedInputs.LedgerState base N C) :
    letI : ProverRwFull.ExternalTypes := PDict_CodecDictionary.native base
    PV_RunJoin_NominalCompiledData.unCompiled base
      ((PV_RunJoin_NativeSelectedInputs.ledgerInputs base ops hash i).compiled s) = i.compiled := by
  letI : ProverRwFull.ExternalTypes := PDict_CodecDictionary.native base
  exact PV_RunJoin_NominalCompiledData.compiled_roundtrip base i.compiled
#print axioms complete_compiled

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K] [CharP K 2147483647]

/-- Actual ledger-body public/compiled coordinates associate with the SAME
honest canonical instance, before the source body executes. No native effect
interpreter or deployed selection is installed by these data equations. -/
theorem coordinates (i : Honest (K := K))
    (s : PV_RunJoin_NativeSelectedInputs.LedgerState base N C) :
    letI : ProverRwFull.ExternalTypes := PDict_CodecDictionary.native base
    PV_RunJoin_SelectedCoordinates32.semantic base
      ((PV_RunJoin_NativeSelectedInputs.ledgerInputs base ops hash i.val).pub s) =
      BuilderSource.prover.public (target i) ∧
    PV_Src_NativeInput.columns PV_Src_Forest_Columns.read
      ((PV_RunJoin_NativeSelectedInputs.ledgerInputs base ops hash i.val).compiled s).semantic_c1.c1 =
      BuilderSource.prover.build (target i) := by
  letI : ProverRwFull.ExternalTypes := PDict_CodecDictionary.native base
  exact ⟨PV_RunJoin_SelectedCoordinates32.public_coordinate base i,build_eq i⟩
#print axioms coordinates
end R1Z.PV_RunJoin_LedgerCaller32
