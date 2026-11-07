import NMX_OwnedPackets
set_option autoImplicit false
noncomputable section
namespace NMX_Program
open Aeneas Aeneas.Std AdapterRw NMX_OwnedPackets
abbrev Account := r1_pool_adapter.owned.OwnedAccount
abbrev Key := solana_pubkey.Pubkey
/-- Every effectful occurrence carries its SAME source arguments. Pure std
reductions remain raw Result operations; their failures are not Rust Err. -/
inductive Command : Type → Type 1 where
 | raw {A : Type} (value : Result A) : Command A
 | readonlyBuffer (account : Account) : Command Unit
 | checkpointGuard (account : Account) (program : Key) (writable : Bool) : Command Unit
 | readonlyAccount (account : Account) (owner : Key) : Command Unit
 | distinct (accounts : Array Account 7#usize) : Command Unit
 | data (account : Account) : Command (Slice U8)
 | key (account : Account) : Command Key
 | toBytes (key : Key) : Command (Array U8 32#usize)
 | fromBytes (bytes : Array U8 32#usize) : Command Key
 | asRef (key : Key) : Command (Slice U8)
 | master (bytes : Slice U8) : Command (Box Master)
 | checkpoint (bytes : Slice U8) : Command (Box Checkpoint)
 | lane (bytes : Slice U8) : Command (Box Lane)
 | pda (seeds : Slice (Slice U8)) (program : Key) : Command Key
 | registry (verifier pool : Key) (masterAccount : Account) (master : Master)
   (registry entry : Account) (slot : U64) : Command Unit
 | snapshot (payload : Snapshot) : Command (Box Snapshot)
/-- Finite source term; a stopped child has no continuation or post-world. -/
inductive Program (A : Type) : Type 1 where
 | ret (value : A)
 | reject (error : PE)
 | stop (cause : Stop)
 | step {B : Type} (command : Command B) (next : B → Program A)
def bind {A B : Type} : Program A → (A → Program B) → Program B
 | .ret a, k => k a
 | .reject e, _ => .reject e
 | .stop s, _ => .stop s
 | .step cmd next, k => .step cmd (fun b => bind (next b) k)
instance : Monad Program where
 pure := Program.ret
 bind := bind
abbrev Handler (W E : Type) := {B : Type} → Command B → W → End W E B

def prepend {W E A : Type} (history : List E) : End W E A → End W E A
 | .returned r w es => .returned r w (history ++ es)
 | .stopped es s => .stopped (history ++ es) s

def eval {W E A : Type} (handler : Handler W E) : Program A → W → End W E A
 | .ret a, w => .returned (.Ok a) w []
 | .reject e, w => .returned (.Err e) w []
 | .stop s, _ => .stopped [] s
 | .step cmd next, w =>
   match handler cmd w with
   | .returned (.Ok b) post es => prepend es (eval handler (next b) post)
   | .returned (.Err e) post es => .returned (.Err e) post es
   | .stopped es s => .stopped es s
end NMX_Program
end
