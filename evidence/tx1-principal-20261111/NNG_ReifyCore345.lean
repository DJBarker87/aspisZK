import NNG_ReifyAccounts345
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_ReifyCore345
open Aeneas Aeneas.Std NMT_345

/-- Full Rust word bounds; cMax is the conservative32-bit constructor bound
and is deliberately not used as the full Usize representability condition. -/
def bounds (a : RSL.OwnedAccount) : Prop :=
 (∀ n,a.length=.ok n → n≤Usize.max) ∧ (∀ b,a.bytes=.ok b → b.length≤Usize.max)
def scalar (n : Nat) : Usize :=
 if h : n≤Usize.max then UScalar.ofNatCore n (by scalar_tac) else 0#usize

theorem scalar_value (n : Nat) (h : n≤Usize.max) : (scalar n).val=n := by
 unfold scalar
 rw [dif_pos h]
 simp only [UScalar.ofNatCore_val_eq]
#print axioms scalar_value

def length : Except RSL.ProgramError Nat → core.result.Result Usize PE
 | .ok n=>.Ok (scalar n)
 | .error e=>.Err (NNG_RawErrors345.raw e)
def raw (a : RSL.OwnedAccount) : Account :=
 ⟨LIB_Env.nativeKey a.key,LIB_Env.nativeKey a.owner,a.is_signer,a.is_writable,a.executable,
 length a.length,NNG_ReifyAccounts345.bytes a.bytes⟩

theorem length_source (x : Except RSL.ProgramError Nat)
 (h : ∀ n,x=.ok n → n≤Usize.max) : rustResult (fun n : Usize=>n.val) (length x)=x := by
 cases x with
 | error e=>exact congrArg Except.error (NNG_RawErrors345.source e)
 | ok n=>exact congrArg Except.ok (scalar_value n (h n rfl))
#print axioms length_source

theorem source (a : RSL.OwnedAccount) (h : bounds a) : account (raw a)=a := by
 unfold raw account
 dsimp only
 rw [NNG_ReifyAccounts345.key_source,NNG_ReifyAccounts345.key_source,
  length_source a.length h.1,NNG_ReifyAccounts345.bytes_source a.bytes h.2]
#print axioms source

def ArgsBounds (a : RSL.TX1_345.Args) : Prop :=
 a.accounts.length≤Usize.max ∧ a.data.length≤Usize.max ∧ ∀ acc∈a.accounts,bounds acc

def input (a : RSL.TX1_345.Args) (h : ArgsBounds a) : Parent Unit :=
 ⟨LIB_Env.nativeKey a.program_id,⟨a.accounts.map raw,by simpa only [List.length_map] using h.1⟩,
  LIBC_Bytes.raw a.data,(),[]⟩

theorem inverse (a : RSL.TX1_345.Args) (h : ArgsBounds a) : NNG_ProjectFrames345.original (input a h)=a := by
 have accounts : (a.accounts.map raw).map account=a.accounts := by
  rw [List.map_map]
  calc
   _ = a.accounts.map id := by
    apply List.map_congr_left
    intro acc member
    exact source acc (h.2.2 acc member)
   _ = a.accounts := List.map_id _
 unfold NNG_ProjectFrames345.original input
 dsimp only
 rw [NNG_ReifyAccounts345.key_source,accounts,LIBC_Bytes.to_native a.data h.2.1]
#print axioms inverse
end AspisR1.NNG_ReifyCore345
