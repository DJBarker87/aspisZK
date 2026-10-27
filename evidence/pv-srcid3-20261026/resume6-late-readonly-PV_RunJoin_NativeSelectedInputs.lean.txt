import R1Z.PV_RunJoin_CallerWorld
import R1Z.PV_RunJoin_NominalPublicData
import R1Z.PV_RunJoin_DictionaryIdentity
import R1Z.PV_RunJoin_LedgerSourceBody
import R1Z.PV_RunJoin_PureSourceLift
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_NativeSelectedInputs
open Aeneas Aeneas.Std Result ProverRwFull ProverRwRetryModel
local instance : ProverRwRngCaller.NativeTypes := PV_RunJoin_CallerWorld.nativeTypes
local instance : ProverRwRngCaller.ErasureFns := ⟨fun _ value => .ok value,fun _ value => .ok value⟩

abbrev SourceState (base : ExternalTypes) (N C : Type) :=
  letI : ExternalTypes := PDict_CodecDictionary.native base
  PV_RunJoin_PureSourceLift.State N C
abbrev LedgerState (base : ExternalTypes) (N C : Type) :=
  letI : ExternalTypes := PDict_CodecDictionary.native base
  PV_RunJoin_LedgerBody.State N C

variable {N C : Type}

def inputs (base : ExternalTypes)
    (ops : SourceState base N C → @ExternalFuns (PDict_CodecDictionary.native base))
    (hash : Slice (Slice U8) → Result (Array U8 32#usize)) (i : PV_Src_NativeInput.Input) :
    letI : ExternalTypes := PDict_CodecDictionary.native base
    PV_RunJoin_PureSourceLift.Inputs N C := by
  letI : ExternalTypes := PDict_CodecDictionary.native base
  exact {
    ops := fun s => PDict_CodecDictionary.selected base (ops s)
    pub := fun _ => PV_RunJoin_NominalPublicData.fromInput base i
    compiled := fun _ => PV_RunJoin_NominalCompiledData.compiled base i.compiled
    hash := fun _ => hash }

def ledgerInputs (base : ExternalTypes)
    (ops : LedgerState base N C → @ExternalFuns (PDict_CodecDictionary.native base))
    (hash : Slice (Slice U8) → Result (Array U8 32#usize)) (i : PV_Src_NativeInput.Input) :
    letI : ExternalTypes := PDict_CodecDictionary.native base
    PV_RunJoin_LedgerBody.Inputs N C := by
  letI : ExternalTypes := PDict_CodecDictionary.native base
  exact {
    ops := fun s => PDict_CodecDictionary.selected base (ops s)
    pub := fun _ => PV_RunJoin_NominalPublicData.fromInput base i
    compiled := fun _ => PV_RunJoin_NominalCompiledData.compiled base i.compiled
    hash := fun _ => hash }

theorem same_selected_compilation (base : ExternalTypes)
    (ops : SourceState base N C → @ExternalFuns (PDict_CodecDictionary.native base))
    (hash : Slice (Slice U8) → Result (Array U8 32#usize)) (i : PV_Src_NativeInput.Input)
    (s : SourceState base N C) :
    letI : ExternalTypes := PDict_CodecDictionary.native base
    (inputs base ops hash i).compiled s = PV_RunJoin_NominalCompiledData.compiled base i.compiled := rfl

theorem full_ledger_source (base : ExternalTypes)
    (ops : LedgerState base N C → @ExternalFuns (PDict_CodecDictionary.native base))
    (hash : Slice (Slice U8) → Result (Array U8 32#usize)) (i : PV_Src_NativeInput.Input)
    (schedule : ProverCommitLedger36.Schedule) (unix : Bool) (address : PV_RunJoin_LedgerWorld.Address) :
    letI : ExternalTypes := PDict_CodecDictionary.native base
    PV_RunJoin_UnifiedRetry.BodySourceLaw
      (PV_RunJoin_LedgerSourceBody.sourceBody (ledgerInputs base ops hash i))
      (PV_RunJoin_LedgerBody.body schedule unix address (ledgerInputs base ops hash i)) := by
  letI : ExternalTypes := PDict_CodecDictionary.native base
  apply PV_RunJoin_LedgerSourceBody.source_law
  intro s
  exact PV_RunJoin_DictionaryIdentity.map_error base (ops s)

#print axioms same_selected_compilation
#print axioms full_ledger_source
end R1Z.PV_RunJoin_NativeSelectedInputs
