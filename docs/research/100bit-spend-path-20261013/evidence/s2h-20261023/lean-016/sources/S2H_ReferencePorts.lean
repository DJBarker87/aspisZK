import S2E_Certificate
import S2F_Stage2Certificate
set_option autoImplicit false
open Aeneas Aeneas.Std Result AspisS2OwnedStage1
namespace AspisR1.S2H
open S2E S2E_Reference.S2E_Reference

/-- Explicit ordinary Result dispatch, retaining the outer fail/div carrier.
This is a REFERENCE evaluator combinator, not native SDK or runtime semantics. -/
def onReply {A S : Type} (reply : Result (core.result.Result A PE))
    (state : S) (sdk : SDK) (next : A → Result (CallerResult S)) : Result (CallerResult S) := do
  let result ← reply
  match result with
  | .Ok value => next value
  | .Err error => ok (.Err error,state,sdk)

/-- Outer stage1 evaluator with explicit source-ordered entry and borrow cuts.
The remaining continuation is the actual extracted body, not an arbitrary
successful callback. This does NOT implement F's uninstantiated Step list. -/
def evalStage1 {C S : Type} (ops : S2E_Reference.Ops) (children : Children C S)
    (o : Original S) : Result (CallerResult S) :=
  onReply (shape1 ops o.data (alloc.vec.Vec.len o.sdk.accounts)) o.state o.sdk (fun _ =>
    onReply (admission ops o.program o.sdk) o.state o.sdk (fun _ => do
      let account ← alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice OwnedAccount)
        o.sdk.accounts 2#usize
      let (reply,acquired,guards) ← owned_acquire_checkpoint o.sdk
        {checkpoint:=none,«public»:=none,proof:=none} account.data_slot
      onReply (ok reply) o.state acquired (fun _ => do
        let (result,state,continued) ← checkpoint_continuation ops children o.state acquired o.data
        let released ← owned_release_guards continued guards
        ok (result,state,released))))

/-- All returned errors and outer fail/div outcomes are retained in this port.
No child success, final equality or independently existential cut is a premise. -/
theorem stage1_evaluator_port {C S : Type} (ops : S2E_Reference.Ops)
    (children : Children C S) (o : Original S) :
    evalStage1 ops children o = E ops children o := by
  unfold evalStage1 onReply E stage1
  simp only [core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
    core.convert.FromSame.from,bind_tc_ok]
  congr 1
  funext reply
  cases reply with
  | Err error => rfl
  | Ok value =>
    cases value
    simp only [bind_tc_ok]
    congr 1
    funext reply
    cases reply with
    | Err error => rfl
    | Ok value =>
      cases value
      simp only [bind_tc_ok]
      congr 1
      funext account
      congr 1
      funext acquired
      rcases acquired with ⟨reply,sdk,guards⟩
      cases reply <;> rfl

/-- Exact stage2 header evaluator. Its Ops remain explicit and are not silently
instantiated to the magic, range/index, comparison or public-length semantics. -/
def stage2Header (ops : S2E_Reference.Ops) (sdk : SDK) (data : Slice U8) : Result Bool := do
  if alloc.vec.Vec.len sdk.accounts != 7#usize then ok false else
    let leading ← core.slice.Slice.get (core.slice.index.SliceIndexRangeToUsizeSlice U8)
      data {«end»:=4#usize}
    let magic ← ops.op13
    let magicSlice ← core.array.Array.index (core.ops.index.IndexSlice
      ((S2E_Reference.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice ops) U8)) magic ()
    let mismatch ← core.cmp.PartialEq.ne.trait_default
      ((S2E_Reference.core.option.Option.Insts.CoreCmpPartialEqOption ops)
        (core.cmp.PartialEqShared (S2E_Reference.Slice.Insts.CoreCmpPartialEqSlice
          core.cmp.PartialEqU8))) leading (some magicSlice)
    ok (!mismatch)

def evalStage2 {C S : Type} (ops : S2E_Reference.Ops) (children : Children C S)
    (o : Original S) : Result (CallerResult S) := do
  let admitted ← stage2Header ops o.sdk o.data
  if admitted then
    let cleared ← children.clear_return_data o.state
    let (reply,validatedState) ← children.validate_asq8 cleared o.program o.sdk o.data
    onReply (ok reply) validatedState o.sdk (fun validated => do
      let (result,state,sdk) ← stage2_proof ops children validatedState o.sdk validated
      let finalState ← children.drop_statement state validated.statement
      ok (result,finalState,sdk))
  else ok (.Err solana_program_error.ProgramError.InvalidInstructionData,o.state,o.sdk)

/-- Header, clear, authentication, actual continuation and statement cleanup
port into the extracted reference on the same fixed inputs and child state. -/
theorem stage2_evaluator_port {C S : Type} (ops : S2E_Reference.Ops)
    (children : Children C S) (o : Original S) :
    evalStage2 ops children o = stage2 ops children o.state o.sdk o.program o.data := by
  unfold evalStage2 stage2Header stage2
  dsimp only
  split
  · rfl
  · simp only [bind_tc_ok,bind_assoc_eq]
    congr 1
    funext leading
    congr 1
    funext magic
    congr 1
    funext magicSlice
    congr 1
    funext mismatch
    cases mismatch <;>
      simp only [Bool.not_true,Bool.not_false,Bool.false_eq_true,↓reduceIte,bind_tc_ok,onReply,
        core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
        core.convert.FromSame.from]
    congr 1
    funext cleared
    congr 1
    funext validated
    rcases validated with ⟨reply,state⟩
    cases reply <;> rfl

/-- REFERENCE success yields exactly E's certificate. No native success port
is assumed or proved by this theorem. -/
theorem evalStage1_certificate {C S : Type} (ops : S2E_Reference.Ops)
    (children : Children C S) (o : Original S) (state : S) (sdk : SDK)
    (accepted : evalStage1 ops children o = ok (.Ok (),state,sdk)) :
    Nonempty (ReferenceCertificate ops children o state sdk) := by
  apply reference_certificate ops children o state sdk
  rwa [stage1_evaluator_port] at accepted

theorem evalStage2_certificate {C S : Type} (ops : S2E_Reference.Ops)
    (children : Children C S) (o : Original S) (state : S) (sdk : SDK)
    (accepted : evalStage2 ops children o = ok (.Ok (),state,sdk)) :
    Nonempty (S2F.Stage2Certificate ops children o state sdk) := by
  apply S2F.stage2_certificate ops children o state sdk
  rwa [stage2_evaluator_port] at accepted

#print axioms stage1_evaluator_port
#print axioms stage2_evaluator_port
#print axioms evalStage1_certificate
#print axioms evalStage2_certificate
end AspisR1.S2H
