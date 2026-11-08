import NMX_R4_ByteCut
import NMX_R2_AccountReify
set_option autoImplicit false
noncomputable section
namespace NMX_R4_AccountProjection
open Aeneas Aeneas.Std RSL
open NMX_R3_RegistryByteCut (cut bound)

def length (n : Nat) : Nat := if n ≤ Usize.max then n else 0

def account (a : OwnedAccount) : OwnedAccount :=
 {a with length := a.length.map length, bytes := a.bytes.map cut}

theorem length_bound (n : Nat) : length n ≤ Usize.max := by
 unfold length
 split <;> omega

theorem bounds (a : OwnedAccount) : NMX_R2_AccountReify.Bounds (account a) := by
 constructor
 · intro n h
   cases ha : a.length with
   | error e => simp only [account,ha,Except.map] at h; cases h
   | ok x => simp only [account,ha,Except.map] at h; cases h; exact length_bound x
 · intro b h
   cases ha : a.bytes with
   | error e => simp only [account,ha,Except.map] at h; cases h
   | ok x => simp only [account,ha,Except.map] at h; cases h; exact bound x

theorem length_checkpoint (n : Nat) : (length n != CHECKPOINT_BYTES) = (n != CHECKPOINT_BYTES) := by
 unfold length
 split
 · rfl
 · rename_i large
   have fits : CHECKPOINT_BYTES ≤ Usize.max := by unfold CHECKPOINT_BYTES; scalar_tac
   have ne : n ≠ CHECKPOINT_BYTES := by omega
   have hn : (n != CHECKPOINT_BYTES) = true := by simp [ne]
   rw [hn]
   rfl

theorem checkpoint (a : OwnedAccount) (p : B32) (w : Bool) :
 verifierCheckpoint (account a) p w = verifierCheckpoint a p w := by
 unfold verifierCheckpoint
 change (if decide (a.owner ≠ p) || a.is_signer || a.executable || a.is_writable != w then _ else _) = _
 split
 · rfl
 · cases ha : a.length with
   | error e => simp only [OwnedAccount.data_len,account,ha,Except.map]
   | ok n => simp only [OwnedAccount.data_len,account,ha,Except.map,RS.ofCloned_ok,RS.bind_pure,length_checkpoint]

theorem readonly (a : OwnedAccount) (p : B32) : readonlyAccount (account a) p = readonlyAccount a p := rfl

theorem buffer (a : OwnedAccount) : readonlyBuffer (account a) = readonlyBuffer a := rfl

theorem distinct (accounts : List OwnedAccount) : requireDistinct (accounts.map account) = requireDistinct accounts := by
 have keys : ∀ xs : List OwnedAccount, distinctKeys (xs.map account) = distinctKeys xs := by
  intro xs
  induction xs with
  | nil => rfl
  | cons a rest ih =>
    simp only [List.map_cons,distinctKeys,List.all_map,ih]
    rfl
 unfold requireDistinct
 rw [keys]

#print axioms length_bound
#print axioms bounds
#print axioms length_checkpoint
#print axioms checkpoint
#print axioms readonly
#print axioms buffer
#print axioms distinct
end NMX_R4_AccountProjection
end
