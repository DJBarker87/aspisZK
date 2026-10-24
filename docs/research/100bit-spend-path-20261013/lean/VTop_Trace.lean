import VTop_Model
/-! Typed operation syntax for the adopted dictionary. No argument is serialized,
hashed or replaced by an identifier: Call retains the original typed values.
Only successful external returns append; inner Rust Err is an ordinary value. -/
set_option autoImplicit false
set_option linter.unusedVariables false
namespace AspisR1.VTop_Trace
open Aeneas Aeneas.Std Result VTop_Stages
universe u v
inductive Call : Type → Type 1 where
  | op0 {T : Type} {E : Type} (a0 : (Option T)) (a1 : E) : Call (core.result.Result T E)
  | op1 : Call aspis_core.field.wide_exact.WideExact
  | op2 (a0 : (Slice Std.U8)) : Call (Option aspis_core.field.wide_exact.WideExact)
  | op3 (a0 : (Slice Std.U8)) : Call (core.result.Result transport.Variant verifier.Error)
  | op4 (a0 : (Slice Std.U8)) : Call (core.result.Result Unit verifier.Error)
  | op5 {H : Type} (aspis_coredigestDigest32Inst : aspis_core.digest.Digest32 H) (a0 : (Slice Std.U8)) (a1 : verifier.Prepared) (a2 : (Array Std.U8 32#usize)) (a3 : Std.Usize) (a4 : H) : Call (core.result.Result Unit verifier.Error)
  | op6 (a0 : (Slice Std.U8)) (a1 : verifier.Prepared) (a2 : verifier.Accumulator) (a3 : (Array aspis_core.field.wide_exact.WideExact 29#usize)) (a4 : (Option (verifier.Phase → Result Unit))) (a5 : verifier.QueryGeometry) (a6 : verifier.BatchedWeights) (a7 : Std.Usize) : Call (core.result.Result (verifier.Accumulator × verifier.BatchedWeights) verifier.Error)
  | op7 {H : Type} (aspis_coredigestDigest32Inst : aspis_core.digest.Digest32 H) (a0 : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public) (a1 : (Slice Std.U8)) (a2 : H) (a3 : (Option (verifier.Phase → Result Unit))) (a4 : (Array aspis_core.field.wide_exact.WideExact 29#usize)) : Call ((core.result.Result verifier.Prepared verifier.Error) × (Array aspis_core.field.wide_exact.WideExact 29#usize))
  | op8 {H : Type} (aspis_coredigestDigest32Inst : aspis_core.digest.Digest32 H) (a0 : verifier.Prepared) (a1 : verifier.Accumulator) (a2 : (Slice Std.U8)) (a3 : (Slice Std.U8)) (a4 : H) : Call (alloc.vec.Vec Std.U8)
  | op9 (a0 : verifier.BatchedWeights) (a1 : (Slice aspis_core.field.QM31)) : Call (Slice aspis_core.field.QM31)
  | op10 (a0 : (Slice aspis_core.field.QM31)) : Call (core.result.Result verifier.BatchedWeights verifier.Error)
  | op11 (a0 : (Array Std.U32 22#usize)) (a1 : Std.Usize) (a2 : Std.Usize) : Call (core.result.Result verifier.QueryGeometry verifier.Error)
  | op12 (a0 : transport.Variant) : Call (core.result.Result verifier.Accumulator verifier.Error)
  | op13 (a0 : (Option (verifier.Phase → Result Unit))) (a1 : verifier.Phase) : Call Unit
  | op14 : Call Std.Usize
  | op15 : Call Std.Usize
  | op16 : Call Std.Usize
  | op17 (N : Std.Usize) (a0 : aspis_core.field.wide_exact.WideExact) : Call (Array aspis_core.field.wide_exact.WideExact N)
  | op18 {H : Type} (aspis_coredigestDigest32Inst : aspis_core.digest.Digest32 H) (a0 : (Slice Std.U8)) (a1 : (Slice Std.U8)) (a2 : (Slice Std.U8)) (a3 : transport.Variant) (a4 : H) : Call (core.result.Result (verifier.Prepared × verifier.Accumulator) verifier.Error)
  | op19 (a0 : verifier.View) (a1 : verifier.Prepared) (a2 : verifier.Accumulator) (a3 : (Option (verifier.Phase → Result Unit))) : Call (core.result.Result Unit verifier.Error)
  | op20 : Call Std.Usize
  | op21 : Call Std.Usize
  | op22 : Call Std.Usize
  | op23 : Call Std.Usize
  | unwrap32 (a0 : core.result.Result (Array Std.U8 32#usize) core.array.TryFromSliceError) : Call (Array Std.U8 32#usize)

def invoke (ops : VTop_Stages.Ops) {A : Type} : Call A → Result A
  | @Call.op0 T E a0 a1 => ops.op0 (T := T) (E := E) a0 a1
  | .op1 => ops.op1
  | .op2 a0 => ops.op2 a0
  | .op3 a0 => ops.op3 a0
  | .op4 a0 => ops.op4 a0
  | @Call.op5 H aspis_coredigestDigest32Inst a0 a1 a2 a3 a4 => ops.op5 (H := H) aspis_coredigestDigest32Inst a0 a1 a2 a3 a4
  | .op6 a0 a1 a2 a3 a4 a5 a6 a7 => ops.op6 a0 a1 a2 a3 a4 a5 a6 a7
  | @Call.op7 H aspis_coredigestDigest32Inst a0 a1 a2 a3 a4 => ops.op7 (H := H) aspis_coredigestDigest32Inst a0 a1 a2 a3 a4
  | @Call.op8 H aspis_coredigestDigest32Inst a0 a1 a2 a3 a4 => ops.op8 (H := H) aspis_coredigestDigest32Inst a0 a1 a2 a3 a4
  | .op9 a0 a1 => ops.op9 a0 a1
  | .op10 a0 => ops.op10 a0
  | .op11 a0 a1 a2 => ops.op11 a0 a1 a2
  | .op12 a0 => ops.op12 a0
  | .op13 a0 a1 => ops.op13 a0 a1
  | .op14 => ops.op14
  | .op15 => ops.op15
  | .op16 => ops.op16
  | @Call.op17 N a0 => ops.op17 N a0
  | @Call.op18 H aspis_coredigestDigest32Inst a0 a1 a2 a3 a4 => ops.op18 (H := H) aspis_coredigestDigest32Inst a0 a1 a2 a3 a4
  | .op19 a0 a1 a2 a3 => ops.op19 a0 a1 a2 a3
  | .op20 => ops.op20
  | .op21 => ops.op21
  | .op22 => ops.op22
  | .op23 => ops.op23
  | .unwrap32 a0 => ops.unwrap32 a0

def operationId {A : Type} : Call A → Nat
  | @Call.op0 T E a0 a1 => 0
  | .op1 => 1
  | .op2 a0 => 2
  | .op3 a0 => 3
  | .op4 a0 => 4
  | @Call.op5 H aspis_coredigestDigest32Inst a0 a1 a2 a3 a4 => 5
  | .op6 a0 a1 a2 a3 a4 a5 a6 a7 => 6
  | @Call.op7 H aspis_coredigestDigest32Inst a0 a1 a2 a3 a4 => 7
  | @Call.op8 H aspis_coredigestDigest32Inst a0 a1 a2 a3 a4 => 8
  | .op9 a0 a1 => 9
  | .op10 a0 => 10
  | .op11 a0 a1 a2 => 11
  | .op12 a0 => 12
  | .op13 a0 a1 => 13
  | .op14 => 14
  | .op15 => 15
  | .op16 => 16
  | @Call.op17 N a0 => 17
  | @Call.op18 H aspis_coredigestDigest32Inst a0 a1 a2 a3 a4 => 18
  | .op19 a0 a1 a2 a3 => 19
  | .op20 => 20
  | .op21 => 21
  | .op22 => 22
  | .op23 => 23
  | .unwrap32 a0 => 24

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

def erase (ops : VTop_Stages.Ops) {A : Type} : Code A → Result A
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

def run (ops : VTop_Stages.Ops) {A : Type} : Code A → Log → Result (A × Log)
  | .done a, log => ok (a,log)
  | .step r k, log => thenResult r (fun b => run ops (k b) log)
  | .call op k, log => thenResult (invoke ops op) (fun b =>
      run ops (k b) (log ++ [.returned op b]))

theorem erase_run (ops : VTop_Stages.Ops) {A : Type} (p : Code A) (log : Log) :
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
    | fail e => simp only [run,thenResult,forget,erase,h,bind_tc_fail]
    | div => simp only [run,thenResult,forget,erase,h,bind_tc_div]
    | ok b => simpa only [run,thenResult,erase,h,bind_tc_ok] using ih b (log ++ [.returned op b])

theorem run_prefix (ops : VTop_Stages.Ops) {A : Type} (p : Code A)
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

theorem erase_perform (ops : VTop_Stages.Ops) {A : Type} (op : Call A) :
    erase ops (perform op) = invoke ops op := by
  cases h : invoke ops op <;> simp only [perform,erase,h,bind_tc_ok,bind_tc_fail,bind_tc_div]

theorem erase_lift (ops : VTop_Stages.Ops) {A : Type} (r : Result A) :
    erase ops (liftResult r) = r := by cases r <;> rfl

theorem erase_bind (ops : VTop_Stages.Ops) {A B : Type} (p : Code A) (k : A → Code B) :
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
end AspisR1.VTop_Trace
