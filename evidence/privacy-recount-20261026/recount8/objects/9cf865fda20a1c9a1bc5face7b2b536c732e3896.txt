import R1Z.PV_RunJoin_SelectedCoordinates32
import R1Z.PV_RunJoin_NativeSnapshot31
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_NativeCallerFrame32
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
    (ops : PV_RunJoin_NativeSelectedInputs.SourceState base N C →
      @ProverRwFull.ExternalFuns (PDict_CodecDictionary.native base))
    (hash : Slice (Slice U8) → Result (Array U8 32#usize))

theorem complete_public (i : PV_Src_NativeInput.Input)
    (s : PV_RunJoin_NativeSelectedInputs.SourceState base N C) :
    letI : ProverRwFull.ExternalTypes := PDict_CodecDictionary.native base
    PV_RunJoin_NativePublicInverse32.unPublic base
      ((PV_RunJoin_NativeSelectedInputs.inputs base ops hash i).pub s) =
      PV_Src_NativeInput.publicInput i := by
  letI : ProverRwFull.ExternalTypes := PDict_CodecDictionary.native base
  exact PV_RunJoin_NativePublicInverse32.from_input_roundtrip base i
#print axioms complete_public

theorem complete_compiled (i : PV_Src_NativeInput.Input)
    (s : PV_RunJoin_NativeSelectedInputs.SourceState base N C) :
    letI : ProverRwFull.ExternalTypes := PDict_CodecDictionary.native base
    PV_RunJoin_NominalCompiledData.unCompiled base
      ((PV_RunJoin_NativeSelectedInputs.inputs base ops hash i).compiled s) = i.compiled := by
  letI : ProverRwFull.ExternalTypes := PDict_CodecDictionary.native base
  exact PV_RunJoin_NominalCompiledData.compiled_roundtrip base i.compiled
#print axioms complete_compiled

/-- The public and compiled arguments carry the SAME full transition for
both variants, before any semantic projection or guard assumption. -/
theorem same_transition (i : PV_Src_NativeInput.Input)
    (s : PV_RunJoin_NativeSelectedInputs.SourceState base N C) :
    letI : ProverRwFull.ExternalTypes := PDict_CodecDictionary.native base
    publicTransition base ((PV_RunJoin_NativeSelectedInputs.inputs base ops hash i).pub s) =
      ((PV_RunJoin_NativeSelectedInputs.inputs base ops hash i).compiled s).public_statement := by
  letI : ProverRwFull.ExternalTypes := PDict_CodecDictionary.native base
  cases i with
  | mk request witness change lane snapshot compiled => cases request <;> rfl
#print axioms same_transition

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K] [CharP K 2147483647]

/-- Complete initial snapshot and candidate afterstate of the actual caller
public argument, derived for the same successful returned compilation. -/
theorem transition_frame (i : Honest (K := K))
    (s : PV_RunJoin_NativeSelectedInputs.SourceState base N C) :
    letI : ProverRwFull.ExternalTypes := PDict_CodecDictionary.native base
    publicTransition base ((PV_RunJoin_NativeSelectedInputs.inputs base ops hash i.val).pub s) =
      ⟨PV_RunJoin_NominalLeafData.snapshot i.val.snapshot,
        PV_RunJoin_NominalLeafData.afterstate i.val.compiled.trace.afterstate⟩ := by
  letI : ProverRwFull.ExternalTypes := PDict_CodecDictionary.native base
  rw [same_transition]
  exact congrArg (PV_RunJoin_NominalPublicData.publicTransition base) (transition i)
#print axioms transition_frame

/-- Complete source payload recovery also retains the private direction,
value-bit and variant frame; no success/error layer is replaced. -/
theorem compiler_frame (i : Honest (K := K))
    (s : PV_RunJoin_NativeSelectedInputs.SourceState base N C) :
    letI : ProverRwFull.ExternalTypes := PDict_CodecDictionary.native base
    let c := PV_RunJoin_NominalCompiledData.unCompiled base
      ((PV_RunJoin_NativeSelectedInputs.inputs base ops hash i.val).compiled s)
    c.trace.private_directions = BuilderRecordsPath.bits (PV_Src_NativeDirections.reference i.val.witness) ∧
    c.trace.value_bits = Array.make 3#usize
      [PV_RunJoin_ValueBits20.bits i.val.witness.pair.value,
       PV_RunJoin_ValueBits20.bits (PV_Src_NativeInput.outputValue i.val.request),
       PV_RunJoin_ValueBits20.bits i.val.change.value] ∧
    c.trace.variant = (match i.val.request with | .transfer _ _ => .PrivateTransfer | .withdrawal _ => .Withdrawal) := by
  letI : ProverRwFull.ExternalTypes := PDict_CodecDictionary.native base
  dsimp only
  rw [complete_compiled]
  exact PV_RunJoin_HonestIdentification26.compiler_frame i
#print axioms compiler_frame
end R1Z.PV_RunJoin_NativeCallerFrame32
