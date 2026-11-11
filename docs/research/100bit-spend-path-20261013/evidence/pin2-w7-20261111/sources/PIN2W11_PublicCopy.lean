import RPv_FJa_PublicCopy
import RPv_FIw_PublicModel
import PublicExtractedRawBridge431
/-! PIN2 W11 (2026-11-11).  `FIw_PublicModel.Public` is now the PIN2 `PIN2P.SemanticPublic`
(W3c; probe-crate emission of the struct only).  Release consumers apply
`FIw_PublicModel.ofPublic` to `FJa_PublicCopy.native q`, the value of the ORIGINAL installed
semantic-public constructor (pre-PIN2 struct, no destination).  `nativePIN2 q` is the same
nine fields plus `destination`, set as the PIN2 Rust constructors set it
(crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs at c7593d23fdc:
`private_public` -> `destination: None`, `withdrawal_public` ->
`destination: Some(public.destination_token_account)`).
`drop` ties it to the extracted pre-PIN2 constructor (`FJa_PublicCopy.on_statement`) on the
nine old fields; the destination field is a field copy of the carrier's
`destination_token_account`.  No extraction of the PIN2 constructor itself exists in the
probe emission (struct only), so there is no PIN2 `on_statement`; this is a named value, not
an extraction claim. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.PIN2W11_PublicCopy
open Aeneas Aeneas.Std Result

def destination : FIq_Carriers.Public → Option (Array U8 32#usize)
  | .Transfer _ _ => none
  | .Withdrawal p _ => some p.destination_token_account

/-- The PIN2 semantic public of the carrier: `native` plus the PIN2 `destination`. -/
def nativePIN2 (q : FIq_Carriers.Public) : FIw_PublicModel.Public :=
  { PIN2P.SemanticPublic.embed (FJa_PublicCopy.native q) with destination := destination q }

theorem drop (q : FIq_Carriers.Public) :
    (nativePIN2 q).dropDestination = FJa_PublicCopy.native q := rfl

theorem destination_eq (q : FIq_Carriers.Public) :
    (nativePIN2 q).destination = destination q := rfl

/-- The model byte helper of the probe-crate helpers is the raw bridge's byte. -/
theorem byte_eq : PIN2P.byte = AspisR1PublicSerializer.RawBridge431.rawByte := by
  funext b
  apply Fin.ext
  show b.val % 256 = b.bv.toNat
  have h : b.val < 256 := b.hBounds
  rw [Nat.mod_eq_of_lt h]
  rfl

theorem bytes32_eq (a : Array U8 32#usize) :
    PIN2P.bytes32 a = (AspisR1PublicSerializer.RawBridge431.rawBytes32 a).val := by
  rw [AspisR1PublicSerializer.RawBridge431.rawBytes32_val, ← byte_eq]
  rfl

#print axioms drop
#print axioms destination_eq
#print axioms byte_eq
#print axioms bytes32_eq
end AspisR1.PIN2W11_PublicCopy
end
