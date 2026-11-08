import NNG_RawErrors345
import LIB_Env
import LIBC_Usize
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_ReifyAccounts345
open Aeneas Aeneas.Std NMT_345

def representable (a : RSL.OwnedAccount) : Prop :=
 (∀ n,a.length=.ok n → n≤UScalar.cMax .Usize) ∧
 (∀ b,a.bytes=.ok b → b.length≤Usize.max)

def length : Except RSL.ProgramError Nat → core.result.Result Usize PE
 | .ok n=>.Ok (LIBC_Usize.raw n)
 | .error e=>.Err (NNG_RawErrors345.raw e)
def bytes : Except RSL.ProgramError RSL.Bytes → core.result.Result (Slice U8) PE
 | .ok b=>.Ok (LIBC_Bytes.raw b)
 | .error e=>.Err (NNG_RawErrors345.raw e)
def raw (a : RSL.OwnedAccount) : Account :=
 ⟨LIB_Env.nativeKey a.key,LIB_Env.nativeKey a.owner,a.is_signer,a.is_writable,a.executable,
 length a.length,bytes a.bytes⟩

theorem key_cast (k : Key) : key k=LIB_Carriers.b32 k := by
 cases k with
 | mk bs h=>
  change RSL.B32.mk _ _=RSL.B32.mk _ _
  congr 1
  exact NNG_DecoderGraph345.bytes ⟨bs,by rw [h];scalar_tac⟩
#print axioms key_cast

theorem key_source (k : RSL.B32) : key (LIB_Env.nativeKey k)=k := by
 rw [key_cast,LIB_Env.key_roundtrip]
#print axioms key_source

theorem length_source (x : Except RSL.ProgramError Nat)
 (h : ∀ n,x=.ok n → n≤UScalar.cMax .Usize) :
 rustResult (fun n : Usize=>n.val) (length x)=x := by
 cases x with
 | error e=>exact congrArg Except.error (NNG_RawErrors345.source e)
 | ok n=>exact congrArg Except.ok (LIBC_Usize.raw_val n (h n rfl))
#print axioms length_source

theorem bytes_source (x : Except RSL.ProgramError RSL.Bytes)
 (h : ∀ b,x=.ok b → b.length≤Usize.max) :
 rustResult (fun b : Slice U8=>b.val.map byte) (bytes x)=x := by
 cases x with
 | error e=>exact congrArg Except.error (NNG_RawErrors345.source e)
 | ok b=>
  change Except.ok ((LIBC_Bytes.raw b).val.map byte)=Except.ok b
  rw [NNG_DecoderGraph345.bytes,LIBC_Bytes.to_native b (h b rfl)]
#print axioms bytes_source

theorem source (a : RSL.OwnedAccount) (h : representable a) : account (raw a)=a := by
 unfold raw account
 rw [key_source,key_source,length_source a.length h.1,bytes_source a.bytes h.2]
 cases a
 rfl
#print axioms source
end AspisR1.NNG_ReifyAccounts345
