import R1Z.PV_RunJoin_NativeSelectedInputs
import R1Z.PDict_CurrentCaller
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_SelectedEntry
open Aeneas Aeneas.Std Result ProverRwFull

abbrev Store (base : ExternalTypes) :=
  @aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore (PDict_CodecDictionary.native base)

def call {S : Type} (base : ExternalTypes)
    (ops : @ExternalFuns (PDict_CodecDictionary.native base))
    (account : ProverRwEffectCallback.Account S)
    (hash : Slice (Slice U8) → Result (Array U8 32#usize))
    (i : PV_Src_NativeInput.Input) (store : Store base) (state : S) :=
  @RealR1_client.prove_for_proof_accounts (PDict_CodecDictionary.native base)
    (PDict_CodecDictionary.selected base ops) S account
    (PV_RunJoin_NominalPublicData.fromInput base i)
    (PV_RunJoin_NominalCompiledData.compiled base i.compiled) hash store state

/-- The SAME actual proof-account entry and selected record survive dict10's
seven-field source erasure. This is a source equality; no native observer,
OS availability, or successful compiler call is inferred from it. -/
theorem seven_field_erasure {S : Type} (base : ExternalTypes)
    (ops other : @ExternalFuns (PDict_CodecDictionary.native base))
    (account : ProverRwEffectCallback.Account S)
    (hash : Slice (Slice U8) → Result (Array U8 32#usize))
    (i : PV_Src_NativeInput.Input) (store : Store base) (state : S) :
    @RealR1_client.prove_for_proof_accounts (PDict_CodecDictionary.native base)
      (@PDict_ReachErase.replace (PDict_CodecDictionary.native base)
        (PDict_CodecDictionary.selected base ops) other) S account
      (PV_RunJoin_NominalPublicData.fromInput base i)
      (PV_RunJoin_NominalCompiledData.compiled base i.compiled) hash store state =
    call base ops account hash i store state := by
  unfold call
  rw [PDict_CurrentCaller.seven_field_caller]

#print axioms call
#print axioms seven_field_erasure
end R1Z.PV_RunJoin_SelectedEntry
