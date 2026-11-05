import Lean
import NFY_Part040
import NFY_Part036
import RPz7_S6NativeForestHelpersV1
import RPz7_S6NativeDigestAcceptedInverseV1
import NFY_Part034
import Aeneas

-- BEGIN copied JFs_PublicLane: lean/JFs_PublicLane.lean
set_option autoImplicit false
namespace AspisR1.NFY_JFs_PublicLane
open Aeneas Aeneas.Std Result
open AspisR1TerminalDecoder pool_v1.pair_forest_accounts

theorem encoded : atomic_statement.encode_digest_canonical NFY_JFt_Digest44.value=
    ok NFY_JFs_PaymentDigests.bytes44 :=
  AspisS6NativeDigestAcceptedInverse.accepted_inverse _ _ NFY_JFs_PaymentDigests.decode44

theorem source : pool_v1_pair_forest_output_lane_v1 NFY_JFt_Digest44.value=ok (.Ok 3#u8) := by
  unfold pool_v1_pair_forest_output_lane_v1
  rw [AspisS6NativeForestHelpers.canonical_eq,NFY_JFu_DigestCheck.source _ NFY_JFt_Digest44.canonical]
  simp only [bind_tc_ok,Bool.true_eq,↓reduceIte]
  unfold first_canonical_byte
  rw [encoded]
  rfl

#print axioms encoded
#print axioms source
end AspisR1.NFY_JFs_PublicLane
-- END copied JFs_PublicLane
-- BEGIN copied JFs_PublicValidation: lean/JFs_PublicValidation.lean
set_option autoImplicit false
namespace AspisR1.NFY_JFs_PublicValidation
open Aeneas Aeneas.Std Result
open AspisR1TerminalDecoder pool_v1.pair_forest_terminal

theorem source : validate_pool_v1_pair_forest_terminal_statement_v1 NFY_JFs_PublicValue.value=ok (.Ok ()) := by
  obtain ⟨encoded,contents,payment⟩:=NFY_JFs_PublicEncoders.payment
  obtain ⟨updated,late,length⟩:=NFY_JFs_PublicEncoders.late
  have common : PoolV1PairForestTerminalStatementV1.common NFY_JFs_PublicValue.value=ok NFY_JFs_PublicValue.common := by rfl
  have publicCall : statement_public_common NFY_JFs_PublicValue.value=
      ok (NFY_JFs_PaymentValue.common.pool,NFY_JFs_PaymentValue.common.deployment_domain,
        NFY_JFs_PaymentValue.common.anchor_sequence,NFY_JFs_PaymentValue.common.anchor_root,
        NFY_JFs_PaymentValue.common.nullifier,NFY_JFs_PaymentValue.common.asset_id) := by rfl
  have laneCall : pool_v1.pair_forest_accounts.pool_v1_pair_forest_output_lane_v1
      NFY_JFs_PaymentValue.common.nullifier=ok (.Ok 3#u8) := NFY_JFs_PublicLane.source
  unfold validate_pool_v1_pair_forest_terminal_statement_v1
  rw [common]
  simp only [bind_tc_ok,NFY_JFs_PublicValue.master_nonzero,NFY_JFs_PublicValue.checkpoint_nonzero,
    NFY_JFs_PublicValue.lane_nonzero,Bool.false_eq_true,↓reduceIte,lift,NFY_JFs_PublicComparisons.lane_bound]
  rw [show NFY_JFs_PublicValue.value=.PrivateTransfer NFY_JFs_PublicValue.common NFY_JFs_PaymentValue.value from rfl]
  simp only [payment,bind_tc_ok,AspisR1TerminalDecoder.core.result.Result.map_err,core.result.Result.Insts.CoreOpsTry.branch]
  dsimp only [NFY_JFs_PublicValue.value] at publicCall
  rw [publicCall]
  run_tac do
    for _ in [:8] do
      let g ← Lean.Elab.Tactic.getMainGoal
      let t ← g.getType
      let names := t.getUsedConstants.filter fun n =>
        let s := n.toString
        s.startsWith "AspisR1TerminalDecoder.pool_v1.pair_forest_terminal.validate_pool_v1_pair_forest_terminal_statement_v1" &&
          (s.splitOn ".").any (fun c => c.startsWith "match_")
      if names.isEmpty then break
      let ids := names.map Lean.mkIdent
      Lean.Elab.Tactic.evalTactic (← `(tactic| unfold $[$ids:ident]*))
  try simp (config := { zeta := true, iota := true }) only
  simp only [uncurry,bind_tc_ok,NFY_JFs_PublicComparisons.pool,NFY_JFs_PublicComparisons.domain,
    NFY_JFs_PublicComparisons.snapshot_pool,NFY_JFs_PublicComparisons.anchor,NFY_JFs_PublicComparisons.sequence,
    Bool.false_eq_true,↓reduceIte,laneCall,
    AspisR1TerminalDecoder.core.result.Result.map_err,core.result.Result.Insts.CoreOpsTry.branch,NFY_JFs_PublicComparisons.lane]
  simp only [uncurry,Array.to_slice_mut,lift,bind_tc_ok]
  try simp (config := { zeta := true, iota := true }) only
  have lateCall : pool_v1.pair_tree_profile.encode_pool_v1_pair_late_public_statement_v1
      NFY_JFs_PublicValue.common.lane_transition (Array.to_slice (Array.repeat 1520#usize 0#u8))=
      ok (.Ok (),updated) := late
  rw [lateCall]
  simp only [uncurry,bind_tc_ok,AspisR1TerminalDecoder.core.result.Result.map_err,core.result.Result.Insts.CoreOpsTry.branch]

#print axioms source
end AspisR1.NFY_JFs_PublicValidation
-- END copied JFs_PublicValidation
-- BEGIN copied JHb_Emit: lean/JHb_Emit.lean
set_option autoImplicit false
noncomputable section
namespace AspisR1.NFY_JHb_Emit
open Aeneas Aeneas.Std Result
open AspisR1TerminalDecoder pool_v1.pair_forest_terminal
open S2K
/-- Frozen emit_result control flow with an explicit return-data syscall and
its state. Field construction and codecs are the source S2K definitions.
This is a source model; native syscall/artifact association is not asserted. -/
def source {A E : Type}
    (syscall : S2I.ReturnData.State A E → List U8 → Result (S2I.ReturnData.State A E))
    (state : S2I.ReturnData.State A E) (statement : StatementAdmission.Statement) :
    Result (core.result.Result (S2I.ReturnData.State A E) AdapterRw.solana_program_error.ProgramError) := do
  let result := ResultAdmission.value statement
  let validated ← validate_pool_v1_pair_forest_terminal_result_against_statement_v1 statement result
  match validated with
  | .Err _ => ok (.Err .InvalidInstructionData)
  | .Ok () =>
    let encoded ← encode_pool_v1_pair_forest_terminal_result_v1 result
    match encoded with
    | .Err _ => ok (.Err .InvalidInstructionData)
    | .Ok bytes =>
      if bytes.val.length ≠ 792 then ok (.Err .InvalidInstructionData)
      else if bytes.val.take 4 ≠ [65#u8,83#u8,82#u8,56#u8] then ok (.Err .InvalidInstructionData)
      else do
        let state' ← syscall state bytes.val
        ok (.Ok state')

theorem accepted {A E : Type}
    (syscall : S2I.ReturnData.State A E → List U8 → Result (S2I.ReturnData.State A E))
    (runtime : S2I.ReturnData.RuntimePremise syscall)
    (state : S2I.ReturnData.State A E) (statement : StatementAdmission.Statement)
    (valid : validate_pool_v1_pair_forest_terminal_statement_v1 statement=ok (.Ok ())) :
    source syscall state statement=ok (.Ok (S2I.ReturnData.set state (ResultPayload.bytes statement).val)) := by
  unfold source
  dsimp only
  rw [ResultBinding.validated statement valid,bind_tc_ok]
  rw [ResultPayload.encoded statement valid,bind_tc_ok]
  dsimp only
  rw [if_neg (by exact not_not_intro (ResultPayload.bytes statement).property)]
  rw [if_neg (by exact not_not_intro (ResultHeader.magic statement))]
  rw [runtime,bind_tc_ok]
#print axioms accepted

theorem real {A E : Type}
    (syscall : S2I.ReturnData.State A E → List U8 → Result (S2I.ReturnData.State A E))
    (runtime : S2I.ReturnData.RuntimePremise syscall) (state : S2I.ReturnData.State A E) :
    source syscall state NFY_JFs_PublicValue.value=
      ok (.Ok (S2I.ReturnData.set state (ResultPayload.bytes NFY_JFs_PublicValue.value).val)) :=
  accepted syscall runtime state _ NFY_JFs_PublicValidation.source
#print axioms real
end AspisR1.NFY_JHb_Emit
end
-- END copied JHb_Emit
-- BEGIN copied JHd_Discriminant: lean/JHd_Discriminant.lean

/-! Aeneas discriminant readers with enum-qualified instance names for import unions.
The pinned generator supplies both commands; only its anonymous instance name
is changed. Scalar types, explicit tags, generic binders and reader bodies are
preserved. This adapter must be rebuilt when the Aeneas generator is repinned. -/
open Lean Elab Term Meta
open Lean.Parser.Term Lean.Parser.Command

namespace NFY_JHd_Discriminant

syntax (name := JHdNamedDiscriminant) "JHd_discriminant" ident ("["num,*"]")? : attr

initialize JHdNamedDiscriminantAttribute : AttributeImpl ← do
  let attrImpl : AttributeImpl := {
    «name» := `JHdNamedDiscriminant,
    descr := "Emit the Aeneas reader with an enum-qualified instance name",
    add := fun declName stx _ => do
      let (ty, values) ← match stx with
        | `(attr| JHd_discriminant $ty) =>
          pure (← Aeneas.Discriminant.elabTypeToken ty, none)
        | `(attr| JHd_discriminant $ty [$xs,*]) =>
          pure (← Aeneas.Discriminant.elabTypeToken ty,
            some ((xs.getElems.toList.map Syntax.isNatLit?).map Option.get!))
        | _ => throwUnsupportedSyntax
      liftCommandElabM do
        let cmds ← Lean.Elab.Command.liftTermElabM
          (Aeneas.Discriminant.generateReadDiscriminantCmds declName ty values)
        Lean.Elab.Command.elabCommand cmds[0]!
        let instName := mkIdent (declName ++ `instDiscriminant)
        let id ← `(Parser.Command.declId| $instName:ident)
        let inst := cmds[1]!.rewriteBottomUp fun node => Id.run do
          if node.isOfKind ``Lean.Parser.Command.instance then
            return node.setArg 3 (mkNullNode #[id.raw])
          return node
        if inst == cmds[1]! then
          throwError "Pinned Aeneas generator no longer emits an instance command"
        Lean.Elab.Command.elabCommand inst
  }
  registerBuiltinAttribute attrImpl
  pure attrImpl

end NFY_JHd_Discriminant
-- END copied JHd_Discriminant

run_cmd do
 let env ← Lean.getEnv
 env.constants.toList.forM fun (n, ci) => do
  if ci.isTheorem && (env.getModuleIdxFor? n).isNone then
   Lean.Elab.Command.elabCommand (← `(command| #print axioms $(Lean.mkIdent n)))
