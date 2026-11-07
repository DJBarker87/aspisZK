import NMX_R2_AccountListReify
import NMX_R2_CallArguments
set_option autoImplicit false
namespace NMX_R2_ArgsReify
open Aeneas Aeneas.Std NMX_R2_Carrier
/-- Explicit representation facts. They do not replace canonical Domain=True. -/
structure Bounds (a : RSL.TX2_233.Args) : Prop where
 count : a.accounts.length ≤ Usize.max
 accounts : ∀ x ∈ a.accounts, NMX_R2_AccountReify.Bounds x

def fromLong (n : UInt64) : U64 := UScalar.ofNatCore n.toNat (UInt64.toNat_lt n)

theorem long_roundtrip (n : UInt64) : long (fromLong n) = n := by
 simp [long,fromLong,UScalar.ofNatCore_val_eq]

def reify (a : RSL.TX2_233.Args) (h : Bounds a) : NMX_RowSpec_233.Args :=
 ⟨NMX_R2_InverseBytes.fromKey a.verifier_program,
  ⟨NMX_R2_AccountListReify.list a.accounts h.accounts,by
   rw [NMX_R2_AccountListReify.length]; exact h.count⟩,
  NMX_R2_InverseBytes.fromKey a.pool_program,NMX_R2_InverseBytes.fromByte a.output_lane,
  fromLong a.current_slot⟩

theorem roundtrip (a : RSL.TX2_233.Args) (h : Bounds a) :
 NMX_R2_CallArguments.auth (reify a h) = a := by
 cases a
 simp only [reify,NMX_R2_CallArguments.auth,NMX_R2_InverseBytes.key_roundtrip,
  NMX_R2_AccountListReify.image,NMX_R2_InverseBytes.byte_roundtrip,long_roundtrip]
#print axioms long_roundtrip
#print axioms roundtrip
end NMX_R2_ArgsReify
