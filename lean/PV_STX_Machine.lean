import PV_STX_Code
set_option autoImplicit false
namespace PV_STX_Machine
open Aeneas Aeneas.Std PV_STX_Code

/-- These outcomes are independent of source Result errors. Resource answers
remain data. No success/adequacy promise is part of the handler's type. -/
inductive Fault where
  | allocationExhausted
  | stackExhausted
  | threadExhausted
  | panic
  | abort

inductive Answer (A : Type) where
  | returned (r : Result A)
  | fault (f : Fault)
  | pending

structure Reply (W E A : Type) where
  answer : Answer A
  world : W
  events : List E

variable {Op : Type → Type 1} {W E A : Type}
abbrev Handler (Op : Type → Type 1) (W E : Type) := {X : Type} → Op X → W → Reply W E X

inductive Status (Op : Type → Type 1) (A : Type) : Type 1 where
  | running (config : Config Op A)
  | returned (r : Result A)
  | fault (f : Fault)

structure Prefix (Op : Type → Type 1) (W E A : Type) : Type 1 where
  status : Status Op A
  world : W
  events : List E

def resumed (k : {X : Type} → Kont Op A X → X → Sum (Result A) (Config Op A))
    {X : Type} (kont : Kont Op A X) (x : X) : Status Op A :=
  match k kont x with
  | .inl r => .returned r
  | .inr c => .running c

/-- Exactly one source administrative step or one reached external answer.
Failure bypasses the continuation but keeps the post-world and events. A
pending external call keeps its exact request AND continuation for resumption. -/
def step (handler : Handler Op W E) (c : Config Op A) (w : W) : Prefix Op W E A :=
  match c.code with
  | .result (.ok a) => ⟨resumed (@continueWith Op A) c.kont a,w,[]⟩
  | .result (.fail e) => ⟨.returned (.fail e),w,[]⟩
  | .result .div => ⟨.returned .div,w,[]⟩
  | .seq first next => ⟨.running ⟨_,first,.seq next c.kont⟩,w,[]⟩
  | .loop body s => ⟨.running ⟨_,body s,.loop body c.kont⟩,w,[]⟩
  | .call op =>
    let r := handler op w
    match r.answer with
    | .returned (.ok x) => ⟨resumed (@continueWith Op A) c.kont x,r.world,r.events⟩
    | .returned (.fail e) => ⟨.returned (.fail e),r.world,r.events⟩
    | .returned .div => ⟨.returned .div,r.world,r.events⟩
    | .fault f => ⟨.fault f,r.world,r.events⟩
    | .pending => ⟨.running c,r.world,r.events⟩

/-- Fuel counts transitions. Cutoff is running, never source div/fail.
Terminal runs are preserved; arbitrary finite prefixes of nontermination are
available without asserting termination or identifying cutoff with divergence. -/
def advance (handler : Handler Op W E) : Nat → Prefix Op W E A → Prefix Op W E A
  | 0, p => p
  | n+1, p =>
    match p.status with
    | .returned _ => p
    | .fault _ => p
    | .running c =>
      let q := step handler c p.world
      advance handler n ⟨q.status,q.world,p.events ++ q.events⟩

def run (handler : Handler Op W E) (fuel : Nat) (c : Code Op A) (w : W) : Prefix Op W E A :=
  advance handler fuel ⟨.running (start c),w,[]⟩

theorem zero_retains_continuation (handler : Handler Op W E) (c : Code Op A) (w : W) :
    (run handler 0 c w).status = .running (start c) := rfl

theorem failed_call_bypasses {X : Type} (handler : Handler Op W E)
    (op : Op X) (k : Kont Op A X) (w : W) (e : Error)
    (h : (handler op w).answer = .returned (.fail e)) :
    step handler ⟨X,.call op,k⟩ w =
      ⟨.returned (.fail e),(handler op w).world,(handler op w).events⟩ := by
  simp only [step,h]

theorem pending_call_retains {X : Type} (handler : Handler Op W E)
    (op : Op X) (k : Kont Op A X) (w : W)
    (h : (handler op w).answer = .pending) :
    step handler ⟨X,.call op,k⟩ w =
      ⟨.running ⟨X,.call op,k⟩,(handler op w).world,(handler op w).events⟩ := by
  simp only [step,h]

#print axioms zero_retains_continuation
#print axioms failed_call_bypasses
#print axioms pending_call_retains
end PV_STX_Machine
