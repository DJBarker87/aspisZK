import PoolL_CanonicalRoleReject
import PoolL_FreshRoleReject
import PoolL_MarkerRoleReject
import PoolL_CloseReject
import PoolL_AllocateReject
set_option autoImplicit false
noncomputable section
namespace AspisR1.PoolL_Physical
open Aeneas Aeneas.Std Result
abbrev Account := AdapterRw.Cuts.Account
abbrev Key := AdapterRw.solana_pubkey.Pubkey
/-- Key-indexed immutable SDK observation cut. This constructs alias coherence
inside the cut; the native runtime-to-cut interpretation is still required. -/
abbrev Snapshot := Key → Account × Slice U8

def observe (s : Snapshot) (key : Key) : Account := { (s key).1 with key := key }
def bytes (s : Snapshot) (key : Key) : Slice U8 := (s key).2
def readLength (s : Snapshot) (a : Account) : Result Usize := ok (Slice.len (bytes s a.key))
def readEmpty (s : Snapshot) (a : Account) : Result Bool := ok (decide ((bytes s a.key).val.length = 0))
def Occupied (s : Snapshot) (key : Key) : Prop :=
  (bytes s key).val.length = 192 ∨ (bytes s key).val.length = 1768

theorem key_eq (s : Snapshot) (key : Key) : (observe s key).key = key := rfl

theorem actual_length (s : Snapshot) (key : Key) :
    readLength s (observe s key) = ok (Slice.len (bytes s key)) := rfl

theorem not_empty (s : Snapshot) (key : Key) (cp : Occupied s key) :
    readEmpty s (observe s key) = ok false := by
  unfold readEmpty observe
  have nz : (bytes s key).val.length ≠ 0 := by rcases cp with h | h <;> omega
  simp [nz]
#print axioms key_eq
#print axioms actual_length
#print axioms not_empty
end AspisR1.PoolL_Physical
end
