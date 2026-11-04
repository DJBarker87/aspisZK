import R1Z.PV_W_Syntax
import R1Z.ProverRwFullFuns
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_W_SourceSyntax
open PV_W_Syntax PV_W_Threading
open ProverRwFull
open Aeneas.Std
variable [ExternalTypes]

/-- A call thunk retains its arguments before evaluation. The world
interpreter is independent of erase: evaluating this thunk under a fixed
ExternalFuns dictionary is used ONLY for the source-syntax correspondence. -/
structure Op (A : Type) where
  label : String
  source : ExternalFuns → Aeneas.Std.Result A

abbrev P (A : Type) := Program Op Aeneas.Std.Error A

instance : Monad P where
  pure := Program.pure
  bind := thenDo

def invoke {A : Type} (label : String) (f : ExternalFuns → Aeneas.Std.Result A) : P A :=
  .call ⟨label,f⟩ .pure

def erase (ops : ExternalFuns) {A : Type} : P A → Aeneas.Std.Result A
  | .pure a => .ok a
  | .failure e => .fail e
  | .diverge => .div
  | .call op k => Aeneas.Std.bind (op.source ops) (fun a => erase ops (k a))

theorem erase_invoke {A : Type} (ops : ExternalFuns) (label : String)
    (f : ExternalFuns → Aeneas.Std.Result A) : erase ops (invoke label f) = f ops := by
  cases h : f ops <;> simp only [erase,invoke,h,Aeneas.Std.bind]

theorem erase_thenDo {A B : Type} (ops : ExternalFuns)
    (p : P A) (k : A → P B) :
    erase ops (thenDo p k) =
      Aeneas.Std.bind (erase ops p) (fun a => erase ops (k a)) := by
  induction p with
  | pure a => rfl
  | failure e => rfl
  | diverge => rfl
  | call op next ih =>
    cases h : op.source ops <;> simp only [thenDo,erase,h,Aeneas.Std.bind,ih]

theorem erase_bind {A B : Type} (ops : ExternalFuns)
    (p : P A) (k : A → P B) :
    erase ops (p >>= k) = Aeneas.Std.bind (erase ops p) (fun a => erase ops (k a)) :=
  erase_thenDo ops p k

theorem source_bind_congr {A B : Type} (m : Aeneas.Std.Result A)
    (left right : A → Aeneas.Std.Result B) (h : ∀ a, left a = right a) :
    Aeneas.Std.bind m left = Aeneas.Std.bind m right :=
  congrArg (Aeneas.Std.bind m) (funext h)

/- Restrict proof search to a syntactic bind on both sides. Unrestricted
higher-order congrArg search can invent binds and loop at a non-bind goal. -/
open Lean Elab Tactic in
elab "pv_source_bind" : tactic => do
  let target ← instantiateMVars (← getMainTarget)
  unless target.isAppOfArity ``Eq 3 do throwError "expected equality"
  let args := target.getAppArgs
  let isBind (e : Expr) := e.isAppOf ``Aeneas.Std.bind || e.isAppOf ``Bind.bind
  unless isBind args[1]! && isBind args[2]! do throwError "expected two source binds"
  evalTactic (← `(tactic| (apply source_bind_congr; intro x)))

theorem erase_pure {A : Type} (ops : ExternalFuns) (a : A) :
    erase ops (Program.pure a : P A) = .ok a := rfl

theorem erase_coreResult {A X Y : Type} (ops : ExternalFuns)
    (r : core.result.Result X Y) (onOk : X → P A) (onErr : Y → P A) :
    erase ops (match r with | .Ok x => onOk x | .Err e => onErr e) =
      match r with | .Ok x => erase ops (onOk x) | .Err e => erase ops (onErr e) := by
  cases r <;> rfl

theorem erase_controlFlow {A X Y : Type} (ops : ExternalFuns)
    (r : core.ops.control_flow.ControlFlow X Y) (onBreak : X → P A) (onContinue : Y → P A) :
    erase ops (match r with | .Break x => onBreak x | .Continue y => onContinue y) =
      match r with | .Break x => erase ops (onBreak x) | .Continue y => erase ops (onContinue y) := by
  cases r <;> rfl

theorem erase_ite {A : Type} (ops : ExternalFuns) (p : Prop) [Decidable p]
    (yes no : P A) : erase ops (if p then yes else no) =
      if p then erase ops yes else erase ops no := by
  by_cases h : p <;> simp only [h,↓reduceIte]

/-- The source-side dictionary is used at each syntactic call. This theorem
asserts a faithful value erasure, never native purity of the call thunk. -/
def resultOutcome {A : Type} : Aeneas.Std.Result A → Outcome Aeneas.Std.Error A
  | .ok a => .ok a
  | .fail e => .fail e
  | .div => .div

def sourceInterpreter (ops : ExternalFuns) : Interpreter Op Unit Unit Aeneas.Std.Error :=
  fun op => PV_W_Threading.lift (resultOutcome (op.source ops))

theorem source_value {A : Type} (ops : ExternalFuns) (p : P A) :
    (eval (sourceInterpreter ops) p ()).outcome = resultOutcome (erase ops p) := by
  induction p with
  | pure a => rfl
  | failure e => rfl
  | diverge => rfl
  | call op k ih =>
    cases h : op.source ops with
    | ok a => simpa only [eval,sourceInterpreter,PV_W_Threading.lift,PV_W_Threading.bind,resultOutcome,h,erase,Aeneas.Std.bind] using ih a
    | fail e => simp only [eval,sourceInterpreter,PV_W_Threading.lift,PV_W_Threading.bind,resultOutcome,h,erase,Aeneas.Std.bind]
    | div => simp only [eval,sourceInterpreter,PV_W_Threading.lift,PV_W_Threading.bind,resultOutcome,h,erase,Aeneas.Std.bind]

#print axioms erase_invoke
#print axioms erase_thenDo
#print axioms erase_bind
#print axioms source_bind_congr
#print axioms erase_pure
#print axioms erase_coreResult
#print axioms erase_controlFlow
#print axioms erase_ite
#print axioms source_value
end R1Z.PV_W_SourceSyntax
