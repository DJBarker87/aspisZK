import PCC_DepositDecodeReference
set_option autoImplicit false
namespace PCC
open PCA
/-- Frozen POOL:199; encode_digest_canonical()[0] is limb0's low byte. -/
def laneReference (commitment : Digest) : Reference UInt8 := fun s =>
  ⟨s,[],if canonical commitment then
    .ok (UInt8.ofNat ((commitment[0]).toNat % 256 % 8))
    else .error (.forest .NonCanonicalDigest)⟩

def RowSpec_POOL_199 (native : Digest → Reference UInt8) : Prop :=
  Reference.RowSpec (fun _ _ => True) native laneReference
end PCC
