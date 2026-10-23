import S2J_Cut5
set_option autoImplicit false
open Aeneas Aeneas.Std Result AspisS2OwnedStage1
namespace AspisR1.S2J
open S2E S2Trust S2H S2E_Reference.S2E_Reference

def readonlyThen (a : OwnedAccount) (tail : Result PR) : Result PR :=
  if a.is_signer then ok (.Err .InvalidAccountData) else
    if a.is_writable then ok (.Err .InvalidAccountData) else
      if a.executable then ok (.Err .InvalidAccountData) else tail

def checkpointMetadata (ops : S2E_Reference.Ops) (program : Array U8 32#usize)
    (sdk : SDK) (cp : OwnedAccount) : Result PR := do
  let b3 ←
    core.array.equality.PartialEqArray.ne
      core.cmp.PartialEqU8 cp.owner program
  if b3
  then
    ok (core.result.Result.Err
      solana_program_error.ProgramError.InvalidAccountData)
  else
    if cp.is_signer
    then
      ok (core.result.Result.Err
        solana_program_error.ProgramError.InvalidAccountData)
    else
      if cp.executable
      then
        ok (core.result.Result.Err
          solana_program_error.ProgramError.InvalidAccountData)
      else
        if cp.is_writable
        then
          let r ←
            _root_.S2E_Reference.S2E_Reference.owned_data_len sdk cp.data_slot
          let cf ←
            core.result.Result.Insts.CoreOpsTry.branch r
          match cf with
          | core.ops.control_flow.ControlFlow.Continue val =>
            let i ←
              ops.op10
                aspis_r1_cost_probe.transport.Variant.S2
            if val != i
            then
              ok (core.result.Result.Err
                solana_program_error.ProgramError.InvalidAccountData)
            else ok (core.result.Result.Ok ())
          | core.ops.control_flow.ControlFlow.Break residual
            =>
            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
              Unit (core.convert.FromSame
              solana_program_error.ProgramError) residual
        else
          ok (core.result.Result.Err
            solana_program_error.ProgramError.InvalidAccountData)

theorem admission_readonly_port (ops : S2E_Reference.Ops) (program : Array U8 32#usize)
    (sdk : SDK) (p u c : OwnedAccount) :
    afterDistinct ops program sdk p u c =
      readonlyThen p (readonlyThen u (checkpointMetadata ops program sdk c)) := by rfl

def readonlyBad (a : OwnedAccount) : Bool := a.is_signer || a.is_writable || a.executable

theorem readonly_port (a : OwnedAccount) :
    readonlyThen a (ok (.Ok ())) =
      ok (if readonlyBad a then .Err .InvalidAccountData else .Ok ()) := by
  cases h1 : a.is_signer <;> cases h2 : a.is_writable <;> cases h3 : a.executable <;>
    simp [readonlyThen,readonlyBad,h1,h2,h3]

def nativeReadonlyProof {W : Type} (_ : S2F.Step) (n : NativeSelections W) : S2F.Outcome PE (NativeSelections W) :=
  match n.1.1.2 with
  | some p => if readonlyBad p.record then .error .InvalidAccountData n else .next n
  | none => .abort n

def referenceReadonlyProof {C A E : Type} (_ : S2F.Step) (r : OwnedSelections C A E) : S2F.Outcome PE (OwnedSelections C A E) :=
  match r.1.1.2 with
  | some p => match readonlyThen p (ok (.Ok ())) with
    | .ok (.Ok ()) => .next r
    | .ok (.Err e) => .error e r
    | .fail _ | .div => .abort r
  | none => .abort r

theorem cut6_stepLaw {W C A E : Type} (L : Library W (World C A E))
    (observe : W → NativeArguments) (fixed : FixedInvocation) (o : Originals W C A E) :
    S2F.StepLaw (CheckpointSelectionRelated L observe fixed) nativeReadonlyProof referenceReadonlyProof o .readonlyProof := by
  intro n r related
  have hp := related.prior.proof.referenceBound
  unfold nativeReadonlyProof referenceReadonlyProof
  cases np : n.1.1.2 <;> cases rp : r.1.1.2 <;> simp only [np,rp] at hp <;> try contradiction
  · exact .abort related
  · dsimp only
    rw [hp.1,readonly_port]
    split <;> constructor <;> exact related

#print axioms admission_readonly_port
#print axioms readonly_port
#print axioms cut6_stepLaw
end AspisR1.S2J
