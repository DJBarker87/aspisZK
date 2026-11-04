import Lean
import NGK_NFO_ReadModel
import NFY_Part058
import NFY_Part041

set_option autoImplicit false
noncomputable section
namespace NGK_NFO_PoolReturnData
open Aeneas Aeneas.Std Result
open AspisR1TerminalDecoder pool_v1.pair_forest_terminal
abbrev Statement := NFY_NEU_EmitModel.Statement
abbrev Output := NFY_NEU_EmitModel.Output
abbrev Bytes := List U8

/-- Primitive runtime interpretation, scoped to the SAME instruction context
and the exact post-write state. No intervening CPI/state is admitted here.
This is the accepted RuntimeReturnData row, not a theorem about Solana. -/
structure Runtime (Context Key State : Type) where
  write : Context → Key → Bytes → State
  read : Context → State → Option (Key × Bytes)

def RuntimeReturnData {Context Key State : Type}
    (runtime : Runtime Context Key State) : Prop :=
  ∀ context program bytes, bytes.length ≤ 1024 →
    runtime.read context (runtime.write context program bytes) = some (program,bytes)

/-- OPEN native decoder obligation. The imported coherent cohort has the
ASR8 encoder; this job must not silently invent a CLOSED decoder bridge.
This named hypothesis states the accepted-emission roundtrip required below. -/
def DecoderAssociation
    (decode : Bytes → Result (core.result.Result Output NFY_NEU_EmitModel.Error)) : Prop :=
  ∀ s : Statement,
    validate_pool_v1_pair_forest_terminal_statement_v1 s = ok (.Ok ()) →
    decode (AspisR1.S2K.ResultPayload.bytes s).val =
      ok (.Ok (AspisR1.S2K.ResultAdmission.value s))

/-- Exact conditional MODEL join. The native Pool read certificate, its
call-site domain and decoder association must be supplied independently for
hybrid credit. No headline or native extraction premise is discharged here. -/
theorem association {Context Key RuntimeState Accounts Other : Type} [DecidableEq Key]
    (runtime : Runtime Context Key RuntimeState) (law : RuntimeReturnData runtime)
    (context : Context) (selected : Key)
    (decode : Bytes → Result (core.result.Result Output NFY_NEU_EmitModel.Error))
    (decoder : DecoderAssociation decode)
    (state : AspisR1.S2I.ReturnData.State Accounts Other) (s : Statement)
    (valid : validate_pool_v1_pair_forest_terminal_statement_v1 s = ok (.Ok ())) :
    AspisR1.NFY_JHb_Emit.source (fun st bytes => ok (AspisR1.S2I.ReturnData.set st bytes))
      state s = ok (.Ok (AspisR1.S2I.ReturnData.set state
        (AspisR1.S2K.ResultPayload.bytes s).val)) ∧
    NGK_NFO_ReadModel.run selected (.Ok ())
      (runtime.read context (runtime.write context selected
        (AspisR1.S2K.ResultPayload.bytes s).val)) decode =
      ok (.Ok ⟨AspisR1.S2K.ResultAdmission.value s,
        (AspisR1.S2K.ResultPayload.bytes s).val⟩,
        [.clear,.invoke,.read,.decode]) := by
  refine ⟨AspisR1.NFY_JHb_Emit.accepted _ (fun _ _ => rfl) state s valid, ?_⟩
  have width := (AspisR1.S2K.ResultPayload.bytes s).property
  rw [law context selected _ (by rw [width]; decide)]
  exact NGK_NFO_ReadModel.decoded selected _ decode _ width (decoder s valid)

/-- The legacy ASVS length gate cannot accept NFD's SAME ASR8 bytes.
This is an interface mismatch result, never a new wire-format adoption. -/
theorem legacy_width_mismatch (s : Statement) :
    (AspisR1.S2K.ResultPayload.bytes s).val.length ≠ 384 := by
  rw [(AspisR1.S2K.ResultPayload.bytes s).property]
  decide

#print axioms association
#print axioms legacy_width_mismatch
end NGK_NFO_PoolReturnData

run_cmd do
 let env ← Lean.getEnv
 env.constants.toList.forM fun (n, ci) => do
  if ci.isTheorem && (env.getModuleIdxFor? n).isNone then
   Lean.Elab.Command.elabCommand (← `(command| #print axioms $(Lean.mkIdent n)))
