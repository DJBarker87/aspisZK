import NMX_Program
set_option autoImplicit false
noncomputable section
namespace NMX_R4_CallProgram
open Aeneas Aeneas.Std AdapterRw NMX_OwnedPackets
inductive Command : Type → Type 1 where
 | scalar {A : Type} (r : Result A) : Command A
 | child {A : Type} (cmd : NMX_Program.Command A) : Command (core.result.Result A PE)
 | pda (seeds : Slice (Slice U8)) (program : solana_pubkey.Pubkey) :
   Command (core.result.Result solana_pubkey.Pubkey solana_pubkey.PubkeyError)
 | snapshot (payload : Snapshot) : Command (Box Snapshot)
inductive Program (A : Type) : Type 1 where
 | ret (a : A)
 | call {B : Type} (cmd : Command B) (next : B → Program A)
def bind {A B : Type} : Program A → (A → Program B) → Program B
 | .ret a,k => k a
 | .call c next,k => .call c (fun a => bind (next a) k)
instance : Monad Program where
 pure := Program.ret
 bind := bind
def call {A : Type} (c : Command A) : Program A := .call c .ret
def scalar {A : Type} (r : Result A) : Program A := call (.scalar r)
def child {A : Type} (c : NMX_Program.Command A) : Program (core.result.Result A PE) := call (.child c)
def pda (s : Slice (Slice U8)) (p : solana_pubkey.Pubkey) := call (.pda s p)
def snapshot (payload : Snapshot) := call (.snapshot payload)
end NMX_R4_CallProgram
end
