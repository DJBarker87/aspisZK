import PCC_Reference
set_option autoImplicit false
namespace PCC
open PCA
def byte (bytes : Bytes) (i : Nat) : Nat := (bytes[i]?.getD 0).toNat

def le16 (bytes : Bytes) (i : Nat) : Nat := byte bytes i + 256 * byte bytes (i+1)
def le32 (bytes : Bytes) (i : Nat) : UInt32 :=
  UInt32.ofNat (le16 bytes i + 65536 * le16 bytes (i+2))
def wireDigest (bytes : Bytes) (offset : Nat) : Digest :=
  Vector.ofFn (fun i : Fin 8 => le32 bytes (offset+4*i.val))
def canonical (digest : Digest) : Bool := digest.toList.all (fun limb => limb.toNat < 2147483647)
/-- Frozen POOL:309/deposit_transport.rs:103–173. Failed fixed-size
conversions are excluded by the preceding extent checks, an own-input lemma
still required for native association; no successful-conversion premise. -/
def decodeReference (bytes : Bytes) : Reference Request := fun s =>
  let result : Outcome Request :=
    if bytes.length < 80 || bytes.length > 592 then .error (.deposit .WrongLength)
    else if bytes.take 4 != [65,83,56,68] then .error (.deposit .WrongMagic)
    else if byte bytes 4 != 1 then .error (.deposit .WrongVersion)
    else if byte bytes 5 != 0 || (bytes.drop 44).take 4 != [0,0,0,0] then
      .error (.deposit .NonZeroReserved)
    else if le16 bytes 6 > 512 then .error (.deposit .InvalidPayloadLength)
    else if bytes.length != 80 + le16 bytes 6 then .error (.deposit .WrongLength)
    else
      let owner := wireDigest bytes 8
      let salt := wireDigest bytes 48
      if !canonical owner then .error (.deposit .NonCanonicalDigest)
      else if !canonical salt then .error (.deposit .NonCanonicalDigest)
      else
        let amount := le32 bytes 40
        if amount == 0 || amount.toNat >= 1073741824 then .error (.deposit .InvalidAmount)
        else .ok ⟨owner,amount,salt,bytes.drop 80⟩
  ⟨s,[],result⟩

def RowSpec_POOL_309 (native : Bytes → Reference Request) : Prop :=
  Reference.RowSpec (fun bytes _ => bytes.length < 2^64) native decodeReference
end PCC
