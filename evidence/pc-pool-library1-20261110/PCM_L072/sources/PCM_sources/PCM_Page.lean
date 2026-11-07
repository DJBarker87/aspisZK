import PCM_Carriers
set_option autoImplicit false
namespace PCM.Page
open RSL Computation
/-- A successful in-place write is recorded immediately, before any later
bounds failure. Aborts carry this ordered prefix, never a post-abort heap. -/
def patch (a : AccountInfo) (offset : Nat) (bytes : Bytes) : Computation Unit := do
  let s ← get
  let old := s.bytes a
  if offset + bytes.length ≤ old.length then
    write a (old.take offset ++ bytes ++ old.drop (offset+bytes.length))
  else fun _ _ o => o = ⟨.abort,[]⟩
def le16 (n : UInt16) : Bytes := [n.toUInt8,(n >>> 8).toUInt8]
def encodeDigest (d : Digest) : Bytes := d.flatMap fun n =>
  [n.toUInt8,(n >>> 8).toUInt8,(n >>> 16).toUInt8,(n >>> 24).toUInt8]
def writeRoots (a : AccountInfo) : Nat → List Digest → Computation Unit
  | _,[] => Computation.pure ()
  | slot,root::rest => do
    patch a (64+32*slot) (encodeDigest root)
    writeRoots a (slot+1) rest
end PCM.Page
