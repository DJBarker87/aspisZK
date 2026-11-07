import NMX_R3_RegistryEmittedLink
import NND_Carrier
import RSL_TX2_234
set_option autoImplicit false
noncomputable section
namespace NMX_R3_RegistryProgram
open Aeneas Aeneas.Std Result AdapterRw

/-- The two effectful child kinds in this loop-free owned body. Every remaining
source operation is a pure/closed value operation; the source audit enumerates
those operations and its later fold discharges their value laws. -/
inductive Command : Type → Type 1
 | scalar {A : Type} (value : Result A) : Command A
 | data (account : r1_pool_adapter.owned.OwnedAccount) :
   Command (core.result.Result (Slice U8) solana_program_error.ProgramError)
 | pda (seeds : Slice (Slice U8)) (program : solana_pubkey.Pubkey) :
   Command (core.result.Result solana_pubkey.Pubkey solana_pubkey.PubkeyError)

inductive Program (A : Type) : Type 1
 | ret (value : A) : Program A
 | call {B : Type} (command : Command B) (next : B → Program A) : Program A

def bind {A B : Type} (p : Program A) (k : A → Program B) : Program B :=
 match p with
 | .ret a => k a
 | .call c next => .call c (fun b => bind (next b) k)

instance : Monad Program where
 pure := Program.ret
 bind := bind

def call {A : Type} (c : Command A) : Program A := .call c .ret

def scalar {A : Type} (r : Result A) : Program A := call (.scalar r)
def data (a : r1_pool_adapter.owned.OwnedAccount) := call (.data a)
def pda (s : Slice (Slice U8)) (p : solana_pubkey.Pubkey) := call (.pda s p)

def commandValue (ops : Ops) {A : Type} : Command A → Result A
 | .scalar value => value
 | .data account => r1_pool_adapter.owned.OwnedAccount.data ops account
 | .pda seeds program => ops.op38 seeds program

def erase (ops : Ops) {A : Type} : Program A → Result A
 | .ret value => ok value
 | .call c next => do let value ← commandValue ops c; erase ops (next value)

theorem result_assoc {A B C : Type} (r : Result A) (f : A → Result B) (g : B → Result C) :
 ((r >>= f) >>= g) = (r >>= fun a => f a >>= g) := by
 cases r <;> rfl

theorem erase_bind (ops : Ops) {A B : Type} (p : Program A) (k : A → Program B) :
 erase ops (p >>= k) = (do let a ← erase ops p; erase ops (k a)) := by
 induction p with
 | ret value => rfl
 | call c next ih =>
  change (Std.bind (commandValue ops c) (fun value => erase ops (bind (next value) k))) =
   Std.bind (Std.bind (commandValue ops c) (fun value => erase ops (next value)))
    (fun a => erase ops (k a))
  cases h : commandValue ops c with
  | ok a => exact ih a
  | fail e => rfl
  | div => rfl

theorem erase_call (ops : Ops) {A : Type} (c : Command A) :
 erase ops (call c) = commandValue ops c := by
 unfold call erase
 cases commandValue ops c <;> rfl

theorem erase_if (ops : Ops) {A : Type} (p : Prop) [Decidable p] (a b : Program A) :
 erase ops (if p then a else b) = if p then erase ops a else erase ops b := by
 by_cases h : p <;> simp only [h,↓reduceIte]
def control {A B C : Type} (cf : core.ops.control_flow.ControlFlow B C)
 (yes : C → Program A) (no : B → Program A) : Program A :=
 match cf with | .Continue x => yes x | .Break e => no e

theorem erase_control (ops : Ops) {A B C : Type}
 (cf : core.ops.control_flow.ControlFlow B C) (yes : C → Program A) (no : B → Program A) :
 erase ops (control cf yes no) =
 (match cf with | .Continue x => erase ops (yes x) | .Break e => erase ops (no e)) := by
 cases cf <;> rfl

#print axioms erase_control

theorem erase_pure (ops : Ops) {A : Type} (a : A) :
 erase ops (pure a : Program A) = ok a := rfl
#print axioms erase_pure

#print axioms result_assoc
#print axioms erase_bind
#print axioms erase_call
#print axioms erase_if
end NMX_R3_RegistryProgram
end
