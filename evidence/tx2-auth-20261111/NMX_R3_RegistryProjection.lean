import NMX_R3_RegistryByteCut
import NMX_R3_RegistryCarrier
import NND_MasterCarrier
set_option autoImplicit false
noncomputable section
namespace NMX_R3_RegistryProjection
open Aeneas Aeneas.Std AdapterRw NND_Carrier

def account (a : RSL.OwnedAccount) : RSL.OwnedAccount :=
 {a with length := .ok 0, bytes := match a.bytes with
  | .ok b => .ok (NMX_R3_RegistryByteCut.cut b)
  | .error e => .error e}

def nativeAccount (a : RSL.OwnedAccount) : r1_pool_adapter.owned.OwnedAccount :=
 ⟨unkey a.key,unkey a.owner,a.is_signer,a.is_writable,a.executable,.Ok 0#usize,
  match a.bytes with
  | .ok b => .Ok (LIBB_Bytes.fromBytes (NMX_R3_RegistryByteCut.cut b) (NMX_R3_RegistryByteCut.bound b))
  | .error e => .Err (unerror e)⟩

theorem bytes_from (b : RSL.Bytes) (h : b.length ≤ Usize.max) :
 NND_Carrier.bytes (LIBB_Bytes.fromBytes b h) = b := by
 change LIBB_Bytes.bytes (LIBB_Bytes.fromBytes b h) = b
 exact LIBB_Bytes.bytes_from b h

theorem account_image (a : RSL.OwnedAccount) :
 NMX_R3_RegistryCarrier.account (nativeAccount a) = account a := by
 cases a with
 | mk key owner signer writable executable length bytes =>
  cases bytes <;>
   simp only [account,nativeAccount,NMX_R3_RegistryCarrier.account,reply,
    key_forth,error_forth,bytes_from]
  <;> rfl

def nativeMaster (p : RSL.VerifierPolicy) :
 aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestMasterV1 :=
 { bump := 0#u8
   identity :=
    { pool := Array.repeat 32#usize 0#u8
      asset_mint := Array.repeat 32#usize 0#u8
      token_program := Array.repeat 32#usize 0#u8
      asset_id := 0#u32
      deployment_domain := Array.repeat 32#usize 0#u8 }
   verifier_policy := LIBB_PolicyValue.unpolicy p
   initialized_lane_mask := 0#u8
   has_checkpoint := false
   next_checkpoint_sequence := 0#u64
   last_checkpoint_lane_sequences := Array.repeat _ 0#u64 }

theorem master_policy (p : RSL.VerifierPolicy) : (master (nativeMaster p)).verifier_policy = p :=
 LIBB_PolicyValue.forth p

def args (a : RSL.TX2_234.Args) : RSL.TX2_234.Args :=
 { a with
    master_account := account a.master_account
    master := master (nativeMaster a.master.verifier_policy)
    registry_account := account a.registry_account
    entry_account := account a.entry_account }

theorem readonly (a : RSL.OwnedAccount) (p : RSL.B32) :
 RSL.readonlyAccount (account a) p = RSL.readonlyAccount a p := rfl

/-- Canonical extension only: impossible oversized bytes reject in each
supplied decoder. Every native representable byte payload is preserved. -/
theorem read_decode {A : Type} (decode : RSL.Bytes → Option A)
 (law : ∀ b, decode (NMX_R3_RegistryByteCut.cut b) = decode b)
 (a : RSL.OwnedAccount) (k : A → RSL.RS Unit) :
 RSL.RS.bind (RSL.OwnedAccount.data (account a))
  (fun b => RSL.RS.bind (RSL.RS.ofOption (decode b) .invalidAccountData) k) =
 RSL.RS.bind a.data
  (fun b => RSL.RS.bind (RSL.RS.ofOption (decode b) .invalidAccountData) k) := by
 cases hb : a.bytes with
 | ok b =>
  simp only [account,RSL.OwnedAccount.data,hb,RSL.RS.ofCloned_ok,RSL.RS.bind_pure,law]
 | error e => simp only [account,RSL.OwnedAccount.data,hb]

#print axioms bytes_from
#print axioms account_image
#print axioms master_policy
#print axioms readonly
#print axioms read_decode
end NMX_R3_RegistryProjection
end
