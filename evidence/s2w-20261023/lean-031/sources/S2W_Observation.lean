import S2W_OuterErasure
import S2W_TraceFacts
/-! One ordered execution of the fixed extracted owned outer callers.
The snapshot/native-write association and opaque helpers' internal events
are intentionally not inferred from their returned values. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.S2W_Observation
open Aeneas Aeneas.Std Result AdapterRw S2W_Trace S2W_TraceFacts S2W_OuterErasure
abbrev Account := r1_pool_adapter.owned.OwnedAccount
abbrev PE := solana_program_error.ProgramError
abbrev Answer := core.result.Result (alloc.vec.Vec U8) PE

def two (ops : Ops) (program_id : solana_pubkey.Pubkey)
    (accounts1 : Slice Account) (data1 : Slice U8)
    (accounts2 : Slice Account) (data2 : Slice U8)
    (slot : core.result.Result U64 PE) : Code Answer := do
  let first ← S2W_Outer.stage1_owned ops S2W_Outer.traceEffects program_id accounts1 data1
  match first with
  | .Err e => pure (.Err e)
  | .Ok checkpoint =>
    let second ← S2W_Outer.stage2_owned ops S2W_Outer.traceEffects program_id accounts2 data2 slot
    match second with
    | .Err e => pure (.Err e)
    | .Ok _ => pure (.Ok checkpoint)

def untraced (ops : Ops) (program_id : solana_pubkey.Pubkey)
    (accounts1 : Slice Account) (data1 : Slice U8)
    (accounts2 : Slice Account) (data2 : Slice U8)
    (slot : core.result.Result U64 PE) : Result Answer := do
  let first ← r1_pool_adapter.owned.stage1_owned ops program_id accounts1 data1
  match first with
  | .Err e => ok (.Err e)
  | .Ok checkpoint =>
    let second ← r1_pool_adapter.owned.stage2_owned ops program_id accounts2 data2 slot
    match second with
    | .Err e => ok (.Err e)
    | .Ok _ => ok (.Ok checkpoint)

theorem erasure (ops : Ops) (program_id : solana_pubkey.Pubkey)
    (accounts1 : Slice Account) (data1 : Slice U8)
    (accounts2 : Slice Account) (data2 : Slice U8)
    (slot : core.result.Result U64 PE) :
    erase ops (two ops program_id accounts1 data1 accounts2 data2 slot) =
      untraced ops program_id accounts1 data1 accounts2 data2 slot := by
  simp only [two,untraced,erase_bind,stage1_erasure]
  apply congrArg (fun k => r1_pool_adapter.owned.stage1_owned ops program_id accounts1 data1 >>= k)
  funext first
  cases first with
  | Err e => rfl
  | Ok cp =>
    simp only [erase_bind,stage2_erasure]
    apply congrArg (fun k => r1_pool_adapter.owned.stage2_owned ops program_id accounts2 data2 slot >>= k)
    funext second
    cases second <;> rfl

theorem accepted_observation (ops : Ops) (program_id : solana_pubkey.Pubkey)
    (accounts1 : Slice Account) (data1 : Slice U8)
    (accounts2 : Slice Account) (data2 : Slice U8)
    (slot : core.result.Result U64 PE) (checkpoint : alloc.vec.Vec U8)
    (accepted1 : r1_pool_adapter.owned.stage1_owned ops program_id accounts1 data1 =
      ok (.Ok checkpoint))
    (accepted2 : r1_pool_adapter.owned.stage2_owned ops program_id accounts2 data2 slot =
      ok (.Ok ())) :
    ∃ log, run ops (two ops program_id accounts1 data1 accounts2 data2 slot) [] =
      ok (.Ok checkpoint,log) ∧ ∀ e ∈ log, ValidEvent ops e := by
  have success : erase ops (two ops program_id accounts1 data1 accounts2 data2 slot) =
      ok (.Ok checkpoint) := by
    rw [erasure]
    simp only [untraced,accepted1,accepted2,bind_tc_ok]
  obtain ⟨log,observed⟩ := success_exists ops _ [] _ success
  exact ⟨log,observed,run_valid ops _ [] log _ (by simp) observed⟩

theorem accepted_segments (ops : Ops) (program_id : solana_pubkey.Pubkey)
    (accounts1 : Slice Account) (data1 : Slice U8)
    (accounts2 : Slice Account) (data2 : Slice U8)
    (slot : core.result.Result U64 PE) (checkpoint : alloc.vec.Vec U8)
    (accepted1 : r1_pool_adapter.owned.stage1_owned ops program_id accounts1 data1 =
      ok (.Ok checkpoint))
    (accepted2 : r1_pool_adapter.owned.stage2_owned ops program_id accounts2 data2 slot =
      ok (.Ok ())) :
    ∃ firstLog finalLog suffix,
      run ops (S2W_Outer.stage1_owned ops S2W_Outer.traceEffects program_id accounts1 data1)
        [] = ok (.Ok checkpoint,firstLog) ∧
      run ops (S2W_Outer.stage2_owned ops S2W_Outer.traceEffects program_id accounts2 data2 slot)
        firstLog = ok (.Ok (),finalLog) ∧
      run ops (two ops program_id accounts1 data1 accounts2 data2 slot) [] =
        ok (.Ok checkpoint,finalLog) ∧
      finalLog = firstLog ++ suffix := by
  obtain ⟨firstLog,first⟩ := success_exists ops
    (S2W_Outer.stage1_owned ops S2W_Outer.traceEffects program_id accounts1 data1) []
    (.Ok checkpoint) ((stage1_erasure ops program_id accounts1 data1).trans accepted1)
  obtain ⟨finalLog,second⟩ := success_exists ops
    (S2W_Outer.stage2_owned ops S2W_Outer.traceEffects program_id accounts2 data2 slot)
    firstLog (.Ok ()) ((stage2_erasure ops program_id accounts2 data2 slot).trans accepted2)
  obtain ⟨suffix,extension⟩ := run_prefix ops
    (S2W_Outer.stage2_owned ops S2W_Outer.traceEffects program_id accounts2 data2 slot)
    firstLog finalLog (.Ok ()) second
  refine ⟨firstLog,finalLog,suffix,first,second,?_,extension⟩
  simp only [two,S2W_TraceFacts.run_bind,first,second,thenResult,run]

#print axioms accepted_segments
#print axioms erasure
#print axioms accepted_observation
end AspisR1.S2W_Observation
