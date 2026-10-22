import AspisR1SolanaDigestWrapperCut.Types
import S4SolanaDigestP3RegroupV1
import AspisR1CurrentCaller.Types

open Aeneas Aeneas.Std Result

namespace S4SolanaDigestWrapperP3BindingV1

abbrev PublicDigest32 (Self : Type) :=
  AspisR1PublicPreparation.aspis_core.Digest32 Self
abbrev CurrentDigest32 (Self : Type) :=
  AspisR1CurrentCaller.aspis_core.digest.Digest32 Self
abbrev SolanaDigest := AspisR1SolanaDigestWrapperCut.SolanaDigest

/-- `SolanaDigest` is the emitted unit struct. This is its source-derived
    Clone/Copy interpretation; LLBC confirms the Rust `#[derive(Clone, Copy]`. -/
def solanaDigestClone (x : SolanaDigest) : Result SolanaDigest := ok x
def solanaDigestCloneInst : core.clone.Clone SolanaDigest :=
  { clone := solanaDigestClone }
def solanaDigestCopyInst : core.marker.Copy SolanaDigest :=
  { cloneInst := solanaDigestCloneInst }

end S4SolanaDigestWrapperP3BindingV1

namespace AspisR1SolanaDigestWrapperCut

/-- Retain the exact emitted `Hash::to_bytes` implementation. -/
def solana_hash.Hash.to_bytes
    (self : solana_hash.Hash) : Result (Array Std.U8 32#usize) := do
  ok self

/-- Functionalized source adapter for the emitted `SolanaDigest::digest`
    body. Relative to the emitted method, only the hashv callee is an explicit
    argument; the bind, output conversion, and ordering are unchanged. -/
def digest_with_hashv
    (hashv : Slice (Slice Std.U8) → Result solana_hash.Hash)
    (self : _root_.S4SolanaDigestWrapperP3BindingV1.SolanaDigest)
    (parts : Slice (Slice Std.U8)) :
    Result (Array Std.U8 32#usize) := do
  let h ← hashv parts
  solana_hash.Hash.to_bytes h

end AspisR1SolanaDigestWrapperCut

namespace S4SolanaDigestWrapperP3BindingV1

/-- The explicit P3 interpretation of the one external hashv operation. -/
def hashvP3
    (sha256 : AspisV8R19.DuplexFrames.Bytes → Array U8 32#usize)
    (parts : Slice (Slice Std.U8)) : Result
      AspisR1SolanaDigestWrapperCut.solana_hash.Hash :=
  ok (sha256 (AspisV8R19.SqueezeOracleBridge.flatten parts))

def p3PublicDigest32
    (sha256 : AspisV8R19.DuplexFrames.Bytes → Array U8 32#usize) :
    PublicDigest32 SolanaDigest := {
  coremarkerCopyInst := solanaDigestCopyInst
  digest := fun self parts =>
    AspisR1SolanaDigestWrapperCut.digest_with_hashv
      (hashvP3 sha256) self parts
}

theorem p3_digest_method_eq_model
    (sha256 : AspisV8R19.DuplexFrames.Bytes → Array U8 32#usize)
    (self : SolanaDigest) (parts : Slice (Slice Std.U8)) :
    AspisR1SolanaDigestWrapperCut.digest_with_hashv
        (hashvP3 sha256) self parts =
      (S4SolanaDigestP3RegroupV1.solanaDigestP3Model
        solanaDigestCopyInst sha256).digest self parts := by
  simp [AspisR1SolanaDigestWrapperCut.digest_with_hashv, hashvP3,
    AspisR1SolanaDigestWrapperCut.solana_hash.Hash.to_bytes,
    S4SolanaDigestP3RegroupV1.solanaDigestP3Model]

theorem p3_public_record_eq_model
    (sha256 : AspisV8R19.DuplexFrames.Bytes → Array U8 32#usize) :
    p3PublicDigest32 sha256 =
      S4SolanaDigestP3RegroupV1.solanaDigestP3Model
        solanaDigestCopyInst sha256 := by
  rfl

/-- Fieldwise adapter from the retained public preparation dictionary to the
    current caller's separately generated nominal dictionary. -/
def publicToCurrent {Self : Type} (d : PublicDigest32 Self) :
    CurrentDigest32 Self := {
  coremarkerCopyInst := d.coremarkerCopyInst
  digest := d.digest
}

@[simp] theorem publicToCurrent_copy {Self : Type} (d : PublicDigest32 Self) :
    (publicToCurrent d).coremarkerCopyInst = d.coremarkerCopyInst := rfl
@[simp] theorem publicToCurrent_digest {Self : Type} (d : PublicDigest32 Self)
    (self : Self) (parts : Slice (Slice Std.U8)) :
    (publicToCurrent d).digest self parts = d.digest self parts := rfl

theorem p3_current_record_eq_model
    (sha256 : AspisV8R19.DuplexFrames.Bytes → Array U8 32#usize) :
    publicToCurrent (p3PublicDigest32 sha256) =
      publicToCurrent
        (S4SolanaDigestP3RegroupV1.solanaDigestP3Model
          solanaDigestCopyInst sha256) := by
  exact congrArg publicToCurrent (p3_public_record_eq_model sha256)

#print axioms p3_digest_method_eq_model
#print axioms p3_public_record_eq_model
#print axioms p3_current_record_eq_model
end S4SolanaDigestWrapperP3BindingV1
