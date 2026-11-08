import NNG_Cut345
import NNG_Model345
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_ProjectAccounts345
open Aeneas Aeneas.Std RSL

def length (n : Nat) : Nat := if n≤Usize.max then n else 0
def account (a : OwnedAccount) : OwnedAccount :=
 {a with length:=a.length.map length,bytes:=a.bytes.map NNG_Cut345.cut}
def args (a : TX1_345.Args) : TX1_345.Args := {a with accounts:=a.accounts.map account}

theorem length_bound (n : Nat) : length n≤Usize.max := by
 unfold length
 split <;> omega
#print axioms length_bound

theorem bounds (a : OwnedAccount) : NNG_ReifyAccounts345.representable (account a) := by
 constructor
 · intro n h
   cases ha : a.length with
   | error e=>simp only [account,ha,Except.map] at h;cases h
   | ok x=>simp only [account,ha,Except.map] at h;cases h;exact length_bound x
 · intro b h
   cases ha : a.bytes with
   | error e=>simp only [account,ha,Except.map] at h;cases h
   | ok x=>simp only [account,ha,Except.map] at h;cases h;exact NNG_Cut345.bound x
#print axioms bounds

theorem length_guard (n : Nat) : (length n != CHECKPOINT_BYTES)=(n != CHECKPOINT_BYTES) := by
 unfold length
 split
 · rfl
 · rename_i large
   have fits : CHECKPOINT_BYTES≤Usize.max := by unfold CHECKPOINT_BYTES;scalar_tac
   have wrong : n≠CHECKPOINT_BYTES := by omega
   simp only [bne,beq_iff_eq]
   simp [wrong]
#print axioms length_guard

theorem checkpoint (a : OwnedAccount) (program : B32) :
 NNG_Phases345.checkpointObservation true (account a) program true=
 NNG_Phases345.checkpointObservation true a program true := by
 unfold NNG_Phases345.checkpointObservation
 change (if decide (a.owner≠program) || a.is_signer || a.executable || a.is_writable != true then _ else _) = _
 split
 · rfl
 · cases ha : a.length with
   | error e=>simp only [account,ha,Except.map];rfl
   | ok n=>
    simp only [account,ha,Except.map]
    change NNG_Pure345.check (length n != CHECKPOINT_BYTES) .invalidAccountData=
      NNG_Pure345.check (n != CHECKPOINT_BYTES) .invalidAccountData
    rw [length_guard]
#print axioms checkpoint

theorem buffer (a : OwnedAccount) : readonlyBuffer (account a)=readonlyBuffer a := rfl
#print axioms buffer

theorem distinct (as_ : List OwnedAccount) : requireDistinct (as_.map account)=requireDistinct as_ := by
 have keys (xs : List OwnedAccount) : distinctKeys (xs.map account)=distinctKeys xs := by
  induction xs with
  | nil=>rfl
  | cons a rest ih=>simp only [List.map_cons,distinctKeys,List.all_map,ih];rfl
 unfold requireDistinct
 rw [keys]
#print axioms distinct

theorem badRoute (a : TX1_345.Args) : TX1_345.badRoute (args a)=TX1_345.badRoute a := by
 unfold TX1_345.badRoute args
 simp only [List.length_map]
#print axioms badRoute
end AspisR1.NNG_ProjectAccounts345
