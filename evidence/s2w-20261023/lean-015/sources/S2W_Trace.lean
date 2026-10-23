import AdapterRwModel
/-! Typed operation syntax for the adopted dictionary. No argument is serialized,
hashed or replaced by an identifier: Call retains the original typed values.
Only successful external returns append; inner Rust Err is an ordinary value. -/
set_option autoImplicit false
set_option linter.unusedVariables false
namespace AspisR1.S2W_Trace
open Aeneas Aeneas.Std Result AdapterRw
inductive Call : Type → Type 1 where
  | op0 {T : Type} {U : Type} {N : Std.Usize} (cmpPartialEqInst : core.cmp.PartialEq T U) (a0 : (Slice T)) (a1 : (Array U N)) : Call Bool
  | op1 {T : Type} {U : Type} {N : Std.Usize} (cmpPartialEqInst : core.cmp.PartialEq T U) (a0 : (Slice T)) (a1 : (Array U N)) : Call Bool
  | op2 {T : Type} (cmpPartialEqInst : core.cmp.PartialEq T T) (a0 : (Option T)) (a1 : (Option T)) : Call Bool
  | op3 {T : Type} (a0 : core.ops.range.RangeFull) (a1 : (Slice T)) : Call ((Slice T) × (Slice T → Slice T))
  | op4 {T : Type} (a0 : core.ops.range.RangeFull) (a1 : (Slice T)) : Call (Slice T)
  | op5 {T : Type} (a0 : core.ops.range.RangeFull) (a1 : (MutRawPtr (Slice T))) : Call (MutRawPtr (Slice T))
  | op6 {T : Type} (a0 : core.ops.range.RangeFull) (a1 : (ConstRawPtr (Slice T))) : Call (ConstRawPtr (Slice T))
  | op7 {T : Type} (a0 : core.ops.range.RangeFull) (a1 : (Slice T)) : Call ((Option (Slice T)) × (Option (Slice T) → Slice T))
  | op8 {T : Type} (a0 : core.ops.range.RangeFull) (a1 : (Slice T)) : Call (Option (Slice T))
  | op9 {T : Type} (a0 : (Slice T)) : Call (Option T)
  | op10 {H : Type} (aspis_coredigestDigest32Inst : aspis_core.digest.Digest32 H) (a0 : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public) (a1 : (Slice Std.U8)) (a2 : (Slice Std.U8)) (a3 : Std.Usize) (a4 : H) (a5 : (Option (aspis_r1_cost_probe.verifier.Phase → Result Unit))) : Call (core.result.Result (alloc.vec.Vec Std.U8) aspis_r1_cost_probe.verifier.Error)
  | op11 {H : Type} (aspis_coredigestDigest32Inst : aspis_core.digest.Digest32 H) (a0 : (Slice Std.U8)) (a1 : (Slice Std.U8)) (a2 : (Slice Std.U8)) (a3 : H) (a4 : (Option (aspis_r1_cost_probe.verifier.Phase → Result Unit))) : Call (core.result.Result Unit aspis_r1_cost_probe.verifier.Error)
  | op12 (a0 : aspis_r1_cost_probe.transport.Variant) : Call Std.Usize
  | op13 : Call Std.U8
  | op14 : Call Std.U8
  | op15 (a0 : aspis_statement.pool_v1.format.VerifierPolicyV1) : Call (core.result.Result Unit aspis_statement.pool_v1.format.PoolV1FormatError)
  | op16 : Call Std.U8
  | op17 (a0 : (Array aspis_core.field.M31 8#usize)) : Call (core.result.Result Std.U8 aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestAccountErrorV1)
  | op18 : Call Std.U8
  | op19 : Call Std.Usize
  | op20 (a0 : aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalPaymentV1) : Call (Array aspis_core.field.M31 8#usize)
  | op21 (a0 : aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1) : Call (core.result.Result Unit aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1)
  | op22 (a0 : aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1) : Call (core.result.Result (Array Std.U8 1880#usize) aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1)
  | op23 (a0 : (Slice Std.U8)) : Call (core.result.Result aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalRequestV1 aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1)
  | op24 (a0 : aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1) : Call (core.result.Result (Array Std.U8 688#usize) aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1)
  | op25 (a0 : aspis_statement.pool_v1.verifier_registry.VerifierRegistryV1) : Call Bool
  | op26 (a0 : aspis_statement.pool_v1.verifier_registry.VerifierRegistryV1) : Call Bool
  | op27 (a0 : aspis_statement.pool_v1.verifier_registry.VerifierRegistryV2) : Call Bool
  | op28 (a0 : aspis_statement.pool_v1.verifier_registry.VerifierRegistryV2) : Call Bool
  | op29 (a0 : aspis_statement.pool_v1.verifier_registry.VerifierRegistryEntryV2) (a1 : Std.U64) : Call Bool
  | op30 (a0 : aspis_statement.pool_v1.verifier_registry.VerifierRegistryEntryV1) (a1 : Std.U64) : Call Bool
  | op31 (a0 : (Slice Std.U8)) : Call (core.result.Result aspis_statement.pool_v1.verifier_registry.VerifierRegistryV1 aspis_statement.pool_v1.verifier_registry.PoolV1VerifierRegistryFormatError)
  | op32 (a0 : (Slice Std.U8)) : Call (core.result.Result aspis_statement.pool_v1.verifier_registry.VerifierRegistryEntryV1 aspis_statement.pool_v1.verifier_registry.PoolV1VerifierRegistryFormatError)
  | op33 (a0 : (Slice Std.U8)) : Call (core.result.Result aspis_statement.pool_v1.verifier_registry.VerifierRegistryV2 aspis_statement.pool_v1.verifier_registry.PoolV1VerifierRegistryFormatError)
  | op34 (a0 : (Slice Std.U8)) : Call (core.result.Result aspis_statement.pool_v1.verifier_registry.VerifierRegistryEntryV2 aspis_statement.pool_v1.verifier_registry.PoolV1VerifierRegistryFormatError)
  | op35 (a0 : solana_program_error.ProgramError) : Call solana_program_error.ProgramError
  | op36 (a0 : solana_pubkey.Pubkey) (a1 : solana_pubkey.Pubkey) : Call Bool
  | op37 (a0 : (Array Std.U8 32#usize)) : Call solana_pubkey.Pubkey
  | op38 (a0 : (Slice (Slice Std.U8))) (a1 : solana_pubkey.Pubkey) : Call (core.result.Result solana_pubkey.Pubkey solana_pubkey.PubkeyError)
  | op39 (a0 : solana_pubkey.Pubkey) : Call (Array Std.U8 32#usize)
  | op40 (a0 : solana_pubkey.Pubkey) : Call (Slice Std.U8)
  | op41 : Call solana_pubkey.Pubkey
  | op42 (a0 : SolanaDigest) : Call SolanaDigest
  | op43 (a0 : SolanaDigest) (a1 : (Slice (Slice Std.U8))) : Call (Array Std.U8 32#usize)
  | op44 (a0 : aspis_r1_cost_probe.verifier.Error) : Call solana_program_error.ProgramError
  | op45 : Call (Array Std.U8 32#usize)
  | op46 : Call (Array Std.U8 32#usize)
  | op47 (a0 : (Slice Std.U8)) : Call (core.result.Result aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1 solana_program_error.ProgramError)
  | op48 (a0 : (Slice Std.U8)) : Call (core.result.Result aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestMasterV1 solana_program_error.ProgramError)
  | op49 (a0 : (Slice Std.U8)) : Call (core.result.Result aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestCheckpointV1 solana_program_error.ProgramError)
  | op50 (a0 : (Slice Std.U8)) : Call (core.result.Result aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestLaneStateV1 solana_program_error.ProgramError)
  | op51 (a0 : (Slice Std.U8)) : Call (core.result.Result r1_pool_adapter.ScannedAsqaProof solana_program_error.ProgramError)
  | op52 (a0 : aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalRequestV1) (a1 : r1_pool_adapter.AuthenticatedAsq8Accounts) (a2 : aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1) : Call (core.result.Result aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1 solana_program_error.ProgramError)
  | op53 (a0 : aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1) : Call (core.result.Result Unit solana_program_error.ProgramError)

def invoke (ops : AdapterRw.Ops) {A : Type} : Call A → Result A
  | .op0 cmpPartialEqInst a0 a1 => ops.op0 (T := T) (U := U) (N := N) cmpPartialEqInst a0 a1
  | .op1 cmpPartialEqInst a0 a1 => ops.op1 (T := T) (U := U) (N := N) cmpPartialEqInst a0 a1
  | .op2 cmpPartialEqInst a0 a1 => ops.op2 (T := T) cmpPartialEqInst a0 a1
  | .op3 a0 a1 => ops.op3 (T := T) a0 a1
  | .op4 a0 a1 => ops.op4 (T := T) a0 a1
  | .op5 a0 a1 => ops.op5 (T := T) a0 a1
  | .op6 a0 a1 => ops.op6 (T := T) a0 a1
  | .op7 a0 a1 => ops.op7 (T := T) a0 a1
  | .op8 a0 a1 => ops.op8 (T := T) a0 a1
  | .op9 a0 => ops.op9 (T := T) a0
  | .op10 aspis_coredigestDigest32Inst a0 a1 a2 a3 a4 a5 => ops.op10 (H := H) aspis_coredigestDigest32Inst a0 a1 a2 a3 a4 a5
  | .op11 aspis_coredigestDigest32Inst a0 a1 a2 a3 a4 => ops.op11 (H := H) aspis_coredigestDigest32Inst a0 a1 a2 a3 a4
  | .op12 a0 => ops.op12 a0
  | .op13 => ops.op13 
  | .op14 => ops.op14 
  | .op15 a0 => ops.op15 a0
  | .op16 => ops.op16 
  | .op17 a0 => ops.op17 a0
  | .op18 => ops.op18 
  | .op19 => ops.op19 
  | .op20 a0 => ops.op20 a0
  | .op21 a0 => ops.op21 a0
  | .op22 a0 => ops.op22 a0
  | .op23 a0 => ops.op23 a0
  | .op24 a0 => ops.op24 a0
  | .op25 a0 => ops.op25 a0
  | .op26 a0 => ops.op26 a0
  | .op27 a0 => ops.op27 a0
  | .op28 a0 => ops.op28 a0
  | .op29 a0 a1 => ops.op29 a0 a1
  | .op30 a0 a1 => ops.op30 a0 a1
  | .op31 a0 => ops.op31 a0
  | .op32 a0 => ops.op32 a0
  | .op33 a0 => ops.op33 a0
  | .op34 a0 => ops.op34 a0
  | .op35 a0 => ops.op35 a0
  | .op36 a0 a1 => ops.op36 a0 a1
  | .op37 a0 => ops.op37 a0
  | .op38 a0 a1 => ops.op38 a0 a1
  | .op39 a0 => ops.op39 a0
  | .op40 a0 => ops.op40 a0
  | .op41 => ops.op41 
  | .op42 a0 => ops.op42 a0
  | .op43 a0 a1 => ops.op43 a0 a1
  | .op44 a0 => ops.op44 a0
  | .op45 => ops.op45 
  | .op46 => ops.op46 
  | .op47 a0 => ops.op47 a0
  | .op48 a0 => ops.op48 a0
  | .op49 a0 => ops.op49 a0
  | .op50 a0 => ops.op50 a0
  | .op51 a0 => ops.op51 a0
  | .op52 a0 a1 a2 => ops.op52 a0 a1 a2
  | .op53 a0 => ops.op53 a0

def operationId {A : Type} : Call A → Nat
  | .op0 cmpPartialEqInst a0 a1 => 0
  | .op1 cmpPartialEqInst a0 a1 => 1
  | .op2 cmpPartialEqInst a0 a1 => 2
  | .op3 a0 a1 => 3
  | .op4 a0 a1 => 4
  | .op5 a0 a1 => 5
  | .op6 a0 a1 => 6
  | .op7 a0 a1 => 7
  | .op8 a0 a1 => 8
  | .op9 a0 => 9
  | .op10 aspis_coredigestDigest32Inst a0 a1 a2 a3 a4 a5 => 10
  | .op11 aspis_coredigestDigest32Inst a0 a1 a2 a3 a4 => 11
  | .op12 a0 => 12
  | .op13 => 13
  | .op14 => 14
  | .op15 a0 => 15
  | .op16 => 16
  | .op17 a0 => 17
  | .op18 => 18
  | .op19 => 19
  | .op20 a0 => 20
  | .op21 a0 => 21
  | .op22 a0 => 22
  | .op23 a0 => 23
  | .op24 a0 => 24
  | .op25 a0 => 25
  | .op26 a0 => 26
  | .op27 a0 => 27
  | .op28 a0 => 28
  | .op29 a0 a1 => 29
  | .op30 a0 a1 => 30
  | .op31 a0 => 31
  | .op32 a0 => 32
  | .op33 a0 => 33
  | .op34 a0 => 34
  | .op35 a0 => 35
  | .op36 a0 a1 => 36
  | .op37 a0 => 37
  | .op38 a0 a1 => 38
  | .op39 a0 => 39
  | .op40 a0 => 40
  | .op41 => 41
  | .op42 a0 => 42
  | .op43 a0 a1 => 43
  | .op44 a0 => 44
  | .op45 => 45
  | .op46 => 46
  | .op47 a0 => 47
  | .op48 a0 => 48
  | .op49 a0 => 49
  | .op50 a0 => 50
  | .op51 a0 => 51
  | .op52 a0 a1 a2 => 52
  | .op53 a0 => 53

inductive Event : Type 1 where
  | returned {A : Type} : Call A → A → Event
abbrev Log := List Event
inductive Code (A : Type) : Type 1 where
  | done : A → Code A
  | step {B : Type} : Result B → (B → Code A) → Code A
  | call {B : Type} : Call B → (B → Code A) → Code A

def bind {A B : Type} : Code A → (A → Code B) → Code B
  | .done a, k => k a
  | .step r c, k => .step r (fun b => bind (c b) k)
  | .call op c, k => .call op (fun b => bind (c b) k)
instance : Monad Code where
  pure := Code.done
  bind := bind

def liftResult {A : Type} (r : Result A) : Code A := .step r .done
instance : MonadLift Result Code where
  monadLift := liftResult

def perform {A : Type} (op : Call A) : Code A := .call op .done

def erase (ops : AdapterRw.Ops) {A : Type} : Code A → Result A
  | .done a => ok a
  | .step r k => do let b ← r; erase ops (k b)
  | .call op k => do let b ← invoke ops op; erase ops (k b)

def thenResult {A : Type u} {B : Type v} (r : Result A) (k : A → Result B) : Result B :=
  match r with
  | .ok a => k a
  | .fail e => .fail e
  | .div => .div

def forget {A : Type} (r : Result (A × Log)) : Result A :=
  thenResult r (fun x => ok x.1)

def run (ops : AdapterRw.Ops) {A : Type} : Code A → Log → Result (A × Log)
  | .done a, log => ok (a,log)
  | .step r k, log => thenResult r (fun b => run ops (k b) log)
  | .call op k, log => thenResult (invoke ops op) (fun b =>
      run ops (k b) (log ++ [.returned op b]))

theorem erase_run (ops : AdapterRw.Ops) {A : Type} (p : Code A) (log : Log) :
    forget (run ops p log) = erase ops p := by
  induction p generalizing log with
  | done a => rfl
  | step r k ih =>
    cases r with
    | fail e => rfl
    | div => rfl
    | ok b => exact ih b log
  | call op k ih =>
    cases h : invoke ops op with
    | fail e => simp only [run,thenResult,erase,h,bind_tc_fail]
    | div => simp only [run,thenResult,erase,h,bind_tc_div]
    | ok b => simpa only [run,thenResult,erase,h,bind_tc_ok] using ih b (log ++ [.returned op b])

theorem run_prefix (ops : AdapterRw.Ops) {A : Type} (p : Code A)
    (before after : Log) (a : A) (success : run ops p before = ok (a,after)) :
    ∃ suffix, after = before ++ suffix := by
  induction p generalizing before after with
  | done b =>
    have eq := Result.ok.inj success
    exact ⟨[], by simpa using congrArg Prod.snd eq.symm⟩
  | step r k ih =>
    cases r with
    | fail e => cases success
    | div => cases success
    | ok b => exact ih b before after success
  | call op k ih =>
    cases h : invoke ops op with
    | fail e => simp only [run,thenResult,h]  at success; cases success
    | div => simp only [run,thenResult,h]  at success; cases success
    | ok b =>
      simp only [run,thenResult,h] at success
      obtain ⟨suffix,hs⟩ := ih b _ after success
      exact ⟨.returned op b :: suffix, by simpa only [List.append_assoc,List.singleton_append] using hs⟩

theorem erase_perform (ops : AdapterRw.Ops) {A : Type} (op : Call A) :
    erase ops (perform op) = invoke ops op := by
  cases h : invoke ops op <;> simp only [perform,erase,h,bind_tc_ok,bind_tc_fail,bind_tc_div]

theorem erase_lift (ops : AdapterRw.Ops) {A : Type} (r : Result A) :
    erase ops (liftResult r) = r := by cases r <;> rfl

theorem erase_bind (ops : AdapterRw.Ops) {A B : Type} (p : Code A) (k : A → Code B) :
    erase ops (p >>= k) = (do let a ← erase ops p; erase ops (k a)) := by
  induction p with
  | done a => rfl
  | step r c ih =>
    change (do let b ← r; erase ops (bind (c b) k)) = _
    have h : ∀ b, erase ops (bind (c b) k) =
      (do let a ← erase ops (c b); erase ops (k a)) := ih
    simp only [h,erase]
    cases r <;> rfl
  | call op c ih =>
    change (do let b ← invoke ops op; erase ops (bind (c b) k)) = _
    have h : ∀ b, erase ops (bind (c b) k) =
      (do let a ← erase ops (c b); erase ops (k a)) := ih
    simp only [h,erase]
    cases invoke ops op <;> rfl

#print axioms erase_run
#print axioms run_prefix
#print axioms erase_perform
#print axioms erase_lift
#print axioms erase_bind
end AspisR1.S2W_Trace
