import RSL_Pool
set_option autoImplicit false
namespace PCM
open RSL
/-- CPI metadata is an ordered list, independently of passed AccountInfos. -/
structure Meta where
  key : B32
  signer : Bool
  writable : Bool
structure Instruction where
  program : B32
  accounts : List Meta
  data : Bytes
structure Invocation where
  instruction : Instruction
  infos : List AccountInfo
  seeds : List (List Bytes)
/-- Full current account cells; the SDK state and cell identity are shared with
RSL and NLF. The lamports and owner projections are needed by runtime calls. -/
structure State where
  sdk : SdkState
  lamports : Nat → UInt64
  owners : Nat → B32
  returnData : Option (B32 × Bytes)
  callIndex : Nat
inductive Event where
  | sdk (event : RSL.Event)
  | invoke (call : Invocation)
  | returned (reply : Except ProgramError Unit)
  | getReturnData (reply : Option (B32 × Bytes))
  | clearReturnData
structure Observation (A : Type) where
  exit : RSL.Exit (Except ProgramError A × State)
  events : List Event
abbrev Computation (A : Type) := State → RSL.Env → Observation A → Prop
namespace Computation

def pure {A : Type} (a : A) : Computation A :=
  fun s _ o => o = ⟨.ret (.ok a, s), []⟩
def throw {A : Type} (e : ProgramError) : Computation A :=
  fun s _ o => o = ⟨.ret (.error e, s), []⟩
def bind {A B : Type} (m : Computation A) (k : A → Computation B) : Computation B :=
  fun s env o =>
    (∃ a s1 es o2, m s env ⟨.ret (.ok a, s1), es⟩ ∧ k a s1 env o2 ∧
      o = ⟨o2.exit, es ++ o2.events⟩) ∨
    (∃ e s1 es, m s env ⟨.ret (.error e, s1), es⟩ ∧ o = ⟨.ret (.error e, s1), es⟩) ∨
    (∃ es, m s env ⟨.abort, es⟩ ∧ o = ⟨.abort, es⟩) ∨
    (∃ es, m s env ⟨.diverge, es⟩ ∧ o = ⟨.diverge, es⟩)
instance : Monad Computation where
  pure := pure
  bind := bind

def ofExcept {A : Type} (r : Except ProgramError A) : Computation A :=
  match r with | .ok a => pure a | .error e => throw e

def lift {A : Type} (m : RSL.RS A) : Computation A := fun s env o =>
  ∃ ro, m env ro ∧ o = ⟨match ro.exit with
    | .ret r => .ret (r, s) | .abort => .abort | .diverge => .diverge,
    ro.events.map Event.sdk⟩

def alloc : Computation Unit := lift (RSL.RS.lift RSL.Spec.alloc)
/-- One reservation channel, precisely RSL Env revision 3. -/
def tryReserve : Computation Bool := lift (RSL.RS.lift RSL.Spec.tryReserve)

def check (bad : Bool) (error : ProgramError) : Computation Unit :=
  if bad then throw error else pure ()
def get : Computation State := fun s _ o => o = ⟨.ret (.ok s, s), []⟩
def put (s : State) : Computation Unit := fun _ _ o => o = ⟨.ret (.ok (), s), []⟩
def emit (ev : Event) : Computation Unit := fun s _ o => o = ⟨.ret (.ok (), s), [ev]⟩

def acquire (a : AccountInfo) (k : Kind) : Computation Nat := fun s env o =>
  ∃ ro, RSL.acquire a k s.sdk env ro ∧ o = ⟨match ro.exit with
    | .ret (r, sdk) => .ret (r, {s with sdk := sdk})
    | .abort => .abort | .diverge => .diverge, ro.events.map Event.sdk⟩

def release (a : AccountInfo) (t : Nat) (k : Kind) : Computation Unit := fun s env o =>
  ∃ ro, RSL.release a t k s.sdk env ro ∧ o = ⟨match ro.exit with
    | .ret sdk => .ret (.ok (), {s with sdk := sdk})
    | .abort => .abort | .diverge => .diverge, ro.events.map Event.sdk⟩

/-- Rust guard scope: drop on both returning Results, never invent a suffix
or a post-abort state for a stopped child. -/
def guardScope {A : Type} (a : AccountInfo) (k : Kind)
    (body : Nat → Computation A) : Computation A := fun s env o =>
  bind (acquire a k) (fun t => fun s1 e o1 =>
    (∃ r s2 es ro, body t s1 e ⟨.ret (r,s2),es⟩ ∧ release a t k s2 e ro ∧
      o1 = ⟨(match ro.exit with
        | .ret (_,s3) => .ret (r,s3)
        | .abort => .abort
        | .diverge => .diverge), es ++ ro.events⟩) ∨
    (∃ es, body t s1 e ⟨.abort,es⟩ ∧ o1 = ⟨.abort,es⟩) ∨
    (∃ es, body t s1 e ⟨.diverge,es⟩ ∧ o1 = ⟨.diverge,es⟩)) s env o

/-- copy_from_slice checks lengths and writes the complete cell. -/
def write (a : AccountInfo) (bytes : Bytes) : Computation Unit := fun s _ o =>
  if (s.sdk.cells a.cell).payload.length = bytes.length then
    o = ⟨.ret (.ok (), { s with sdk := s.sdk.put a.cell
      { (s.sdk.cells a.cell) with payload := bytes }}), [.sdk (.write a.cell bytes)]⟩
  else o = ⟨.abort, []⟩
end Computation

/-- A child domain is checked at its actual arguments in the reference. These
parameters are supporting work until installed with CLOSED graphs. -/
structure Child (A B : Type) where
  domain : A → Prop
  law : A → Computation B

def Child.call {A B : Type} (c : Child A B) (a : A) : Computation B :=
  fun s env o => c.domain a ∧ c.law a s env o

/-- Graph form required of every installed deterministic CLOSED child model. -/
def Graph {A B : Type} (domain : A → Prop)
    (model : A → State → Env → Observation B) : A → Computation B :=
  fun a s env o => domain a ∧ o = model a s env

/-- Runtime reply contains an arbitrary post-state; in particular no frame on
passed cells, readonly flag, borrow count, or return-data is supplied here. -/
structure Runtime where
  invoke : Invocation → Computation Unit
  readReturnData : Computation (Option (B32 × Bytes))
  clearReturnData : Computation Unit

/-- Exact, total observation refinement; no empty native invocation relation. -/
def RowSpec {A B : Type} (domain : A → Prop) (reference : A → Computation B)
    (impl : A → State → Env → Observation B) : Prop :=
  ∀ a, domain a → ∀ s env, reference a s env (impl a s env)

/-- Generic graph rejection: changing even a single exact observation is seen. -/
theorem graph_rejects {A B : Type} (domain : A → Prop)
    (model impl : A → State → Env → Observation B) (a : A) (s : State) (env : Env)
    (hd : domain a) (hne : impl a s env ≠ model a s env) :
    ¬ RowSpec domain (Graph domain model) impl := by
  intro h
  exact hne (h a hd s env).2

#print axioms graph_rejects
end PCM
