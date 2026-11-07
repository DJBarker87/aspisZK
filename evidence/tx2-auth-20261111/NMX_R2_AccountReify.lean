import NMX_R2_ErrorModelInverse
import NMX_R2_InverseBytes
set_option autoImplicit false
namespace NMX_R2_AccountReify
open Aeneas Aeneas.Std AdapterRw NMX_R2_Carrier
/-- Rust representability facts, not a RowSpec domain or a protocol condition. -/
structure Bounds (a : RSL.OwnedAccount) : Prop where
 length : ∀ n, a.length = .ok n → n ≤ Usize.max
 bytes : ∀ b, a.bytes = .ok b → b.length ≤ Usize.max

def scalar (n : Nat) (bound : n ≤ Usize.max) : Usize :=
 UScalar.ofNatCore n (by scalar_tac)

theorem scalar_value (n : Nat) (bound : n ≤ Usize.max) : (scalar n bound).val = n := by
 simp only [scalar,UScalar.ofNatCore_val_eq]

def account (a : RSL.OwnedAccount) (bound : Bounds a) : r1_pool_adapter.owned.OwnedAccount :=
 ⟨NMX_R2_InverseBytes.fromKey a.key,NMX_R2_InverseBytes.fromKey a.owner,
  a.is_signer,a.is_writable,a.executable,
  match length : a.length with
  | .error e => .Err (NMX_R2_ErrorInverse.fromError e)
  | .ok n => .Ok (scalar n (bound.length n length)),
  match bytes : a.bytes with
  | .error e => .Err (NMX_R2_ErrorInverse.fromError e)
  | .ok b => .Ok ⟨b.map NMX_R2_InverseBytes.fromByte,by simpa only [List.length_map] using bound.bytes b bytes⟩⟩

theorem roundtrip (a : RSL.OwnedAccount) (bound : Bounds a) :
 NMX_R2_Carrier.account (account a bound) = a := by
 cases a with
 | mk key owner sign write exec length bytes =>
   cases length <;> cases bytes <;>
    simp [account,NMX_R2_Carrier.account,NMX_R2_Carrier.reply,scalar_value,
     NMX_R2_InverseBytes.key_roundtrip,NMX_R2_ErrorModelInverse.error,
     List.map_map,Function.comp_def,NMX_R2_InverseBytes.byte_roundtrip]
#print axioms scalar_value
#print axioms roundtrip
end NMX_R2_AccountReify
