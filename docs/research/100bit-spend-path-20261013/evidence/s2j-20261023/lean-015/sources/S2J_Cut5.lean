import S2J_Cut4
set_option autoImplicit false
open Aeneas Aeneas.Std Result AspisS2OwnedStage1
namespace AspisR1.S2J
noncomputable section
local attribute [instance] Classical.propDecidable
open S2E S2Trust S2H S2E_Reference.S2E_Reference
abbrev PE := solana_program_error.ProgramError
abbrev PR := core.result.Result Unit PE

def distinctThen (proof public1 cp : OwnedAccount) (tail : Result PR) : Result PR := do
  let b ← core.array.equality.PartialEqArray.eq core.cmp.PartialEqU8 proof.key public1.key
  if b then ok (.Err .InvalidArgument) else
    let b1 ← core.array.equality.PartialEqArray.eq core.cmp.PartialEqU8 proof.key cp.key
    if b1 then ok (.Err .InvalidArgument) else
      let b2 ← core.array.equality.PartialEqArray.eq core.cmp.PartialEqU8 public1.key cp.key
      if b2 then ok (.Err .InvalidArgument) else tail

/-- Verbatim remaining extracted admission, factored after its distinct gate. -/
def afterDistinct (ops : S2E_Reference.Ops) (program : Array U8 32#usize)
    (sdk : SDK) (proof public1 cp : OwnedAccount) : Result PR := do
  if proof.is_signer
  then
    ok (core.result.Result.Err
      solana_program_error.ProgramError.InvalidAccountData)
  else
    if proof.is_writable
    then
      ok (core.result.Result.Err
        solana_program_error.ProgramError.InvalidAccountData)
    else
      if proof.executable
      then
        ok (core.result.Result.Err
          solana_program_error.ProgramError.InvalidAccountData)
      else
        if public1.is_signer
        then
          ok (core.result.Result.Err
            solana_program_error.ProgramError.InvalidAccountData)
        else
          if public1.is_writable
          then
            ok (core.result.Result.Err
              solana_program_error.ProgramError.InvalidAccountData)
          else
            if public1.executable
            then
              ok (core.result.Result.Err
                solana_program_error.ProgramError.InvalidAccountData)
            else
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

/-- Definitional port into E, retaining every subsequent SDK/error branch. -/
theorem admission_distinct_port (ops : S2E_Reference.Ops) (program : Array U8 32#usize) (sdk : SDK) :
    admission ops program sdk = (do
      let proof ← alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice OwnedAccount) sdk.accounts 0#usize
      let public1 ← alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice OwnedAccount) sdk.accounts 1#usize
      let cp ← alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice OwnedAccount) sdk.accounts 2#usize
      distinctThen proof public1 cp (afterDistinct ops program sdk proof public1 cp)) := by rfl

theorem key_equality (a b : Array U8 32#usize) :
    core.array.equality.PartialEqArray.eq core.cmp.PartialEqU8 a b = ok (decide (a = b)) := by
  change core.slice.cmp.PartialEqSlice.eq core.cmp.PartialEqU8 a.to_slice b.to_slice = _
  rw [byte_equality]
  simp [Array.to_slice,Subtype.ext_iff]

def duplicate (proof public1 cp : OwnedAccount) : Bool :=
  decide (proof.key = public1.key ∨ proof.key = cp.key ∨ public1.key = cp.key)

theorem distinct_port (proof public1 cp : OwnedAccount) :
    distinctThen proof public1 cp (ok (.Ok ())) =
      ok (if duplicate proof public1 cp then .Err .InvalidArgument else .Ok ()) := by
  unfold distinctThen
  simp only [key_equality,bind_tc_ok]
  by_cases a : proof.key = public1.key <;> by_cases b : proof.key = cp.key <;>
    by_cases c : public1.key = cp.key <;> simp [duplicate,a,b,c]

abbrev NativeSelections (W : Type) := ((W × Option AccountReference) × Option AccountReference) × Option AccountReference
abbrev OwnedSelections (C A E : Type) := ((OwnedCut C A E × Option OwnedAccount) × Option OwnedAccount) × Option OwnedAccount

def nativeDistinct {W : Type} (_ : S2F.Step) (n : NativeSelections W) : S2F.Outcome PE (NativeSelections W) :=
  match n.1.1.2,n.1.2,n.2 with
  | some p,some u,some c => if duplicate p.record u.record c.record then .error .InvalidArgument n else .next n
  | _,_,_ => .abort n

def referenceDistinct {C A E : Type} (_ : S2F.Step) (r : OwnedSelections C A E) : S2F.Outcome PE (OwnedSelections C A E) :=
  match r.1.1.2,r.1.2,r.2 with
  | some p,some u,some c =>
    match distinctThen p u c (ok (.Ok ())) with
    | .ok (.Ok ()) => .next r
    | .ok (.Err e) => .error e r
    | .fail _ | .div => .abort r
  | _,_,_ => .abort r

theorem cut5_stepLaw {W C A E : Type} (L : Library W (World C A E))
    (observe : W → NativeArguments) (fixed : FixedInvocation) (o : Originals W C A E) :
    S2F.StepLaw (CheckpointSelectionRelated L observe fixed) nativeDistinct referenceDistinct o .distinct := by
  intro n r related
  have hp := related.prior.proof.referenceBound
  have hu := related.prior.referenceBound
  have hc := related.referenceBound
  unfold nativeDistinct referenceDistinct
  cases np : n.1.1.2 <;> cases rp : r.1.1.2 <;>
    cases nu : n.1.2 <;> cases ru : r.1.2 <;>
    cases nc : n.2 <;> cases rc : r.2 <;>
    simp only [np,rp] at hp <;> simp only [nu,ru] at hu <;> simp only [nc,rc] at hc <;>
    try contradiction
  all_goals try exact .abort related
  dsimp only
  rw [hp.1,hu.1,hc.1,distinct_port]
  split <;> constructor <;> exact related

#print axioms admission_distinct_port
#print axioms key_equality
#print axioms distinct_port
#print axioms cut5_stepLaw
end AspisR1.S2J
