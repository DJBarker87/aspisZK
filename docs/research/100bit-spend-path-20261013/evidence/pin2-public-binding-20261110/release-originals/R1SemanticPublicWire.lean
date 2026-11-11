import R1PublicFieldBlockCodec
import R1PublicIndexListCodec
import R1PublicByteCursor
import PublicOptionShape

/-! Executable model of the source's section-9 semantic-public layout.
The ASF8 envelope, account binding, and Rust refinement are separate.
This wire carrier fixes the two variants' option shape and bounds the index
to its eight-byte representation; withdrawal nonzero is checked separately. -/
set_option autoImplicit false
namespace AspisR1.SemanticPublicWire

abbrev Byte := ExactLeafFieldCodec.Byte
abbrev M31 := ExactLeafFieldCodec.M31Exact
abbrev Digest := PublicFieldBlockCodec.Digest
abbrev Frontier := PublicFieldBlockCodec.Frontier

structure Common where
  anchor : Digest
  nullifier : Digest
  assetId : M31
  change : Digest
  nextPairIndex : PublicIndexCodec.Index
  snapshotFrontier : Frontier
  nextRoot : Digest
  nextFrontier : Frontier

inductive Wire
  | transfer (common : Common) (recipient : Digest)
  | withdrawal (common : Common) (amount : M31)

def toPublic : Wire → R0P.Public M31
  | .transfer c recipient =>
      ⟨.privateTransfer, c.anchor, c.nullifier, c.assetId, some recipient,
        c.change, none, c.nextPairIndex.val, c.snapshotFrontier, c.nextRoot, c.nextFrontier⟩
  | .withdrawal c amount =>
      ⟨.withdrawal, c.anchor, c.nullifier, c.assetId, none,
        c.change, some amount, c.nextPairIndex.val, c.snapshotFrontier, c.nextRoot, c.nextFrontier⟩

def header (c : Common) : List Byte :=
  PublicFieldBlockCodec.encodeDigest c.anchor ++
    PublicFieldBlockCodec.encodeDigest c.nullifier ++ ExactLeafFieldCodec.encodeM31 c.assetId

def afterBytes (c : Common) : List Byte :=
  PublicIndexListCodec.encode c.nextPairIndex ++
    PublicFieldBlockCodec.encodeFrontier c.snapshotFrontier ++
    PublicFieldBlockCodec.encodeDigest c.nextRoot ++
    PublicFieldBlockCodec.encodeFrontier c.nextFrontier

def encode : Wire → List Byte
  | .transfer c recipient =>
      [0] ++ header c ++ [1] ++ PublicFieldBlockCodec.encodeDigest recipient ++
        PublicFieldBlockCodec.encodeDigest c.change ++ [0] ++ afterBytes c
  | .withdrawal c amount =>
      [1] ++ header c ++ [0] ++ PublicFieldBlockCodec.encodeDigest c.change ++
        [1] ++ ExactLeafFieldCodec.encodeM31 amount ++ afterBytes c

def expect (tag : Byte) : List Byte → Option (List Byte)
  | [] => none
  | x :: xs => if x = tag then some xs else none

def readDigest := PublicByteCursor.read 32 PublicFieldBlockCodec.decodeDigest
def readField := PublicByteCursor.read 4 ExactLeafFieldCodec.decodeM31
def readIndex := PublicByteCursor.read 8 PublicIndexListCodec.decode
def readFrontier := PublicByteCursor.read 640 PublicFieldBlockCodec.decodeFrontier

/-- Read the common suffix and reject trailing bytes. -/
def decodeAfter (anchor nullifier : Digest) (assetId : M31) (change : Digest)
    (bytes : List Byte) : Option Common := do
  let (index, rest) ← readIndex bytes
  let (snapshot, rest) ← readFrontier rest
  let (root, rest) ← readDigest rest
  let (frontier, rest) ← readFrontier rest
  if rest.isEmpty then
    some ⟨anchor, nullifier, assetId, change, index, snapshot, root, frontier⟩
  else none

def decodeTransfer (bytes : List Byte) : Option Wire := do
  let (anchor, rest) ← readDigest bytes
  let (nullifier, rest) ← readDigest rest
  let (asset, rest) ← readField rest
  let rest ← expect 1 rest
  let (recipient, rest) ← readDigest rest
  let (change, rest) ← readDigest rest
  let rest ← expect 0 rest
  let c ← decodeAfter anchor nullifier asset change rest
  some (.transfer c recipient)

def decodeWithdrawal (bytes : List Byte) : Option Wire := do
  let (anchor, rest) ← readDigest bytes
  let (nullifier, rest) ← readDigest rest
  let (asset, rest) ← readField rest
  let rest ← expect 0 rest
  let (change, rest) ← readDigest rest
  let rest ← expect 1 rest
  let (amount, rest) ← readField rest
  let c ← decodeAfter anchor nullifier asset change rest
  some (.withdrawal c amount)

def decode : List Byte → Option Wire
  | [] => none
  | tag :: rest =>
      if tag = 0 then decodeTransfer rest
      else if tag = 1 then decodeWithdrawal rest else none

def parsePublic (bytes : List Byte) : Option (R0P.Public M31) := do
  let wire ← decode bytes
  let pub := toPublic wire
  if PublicOptionShape.check pub then some pub else none

theorem parsePublic_canonical (bytes : List Byte) (pub : R0P.Public M31)
    (h : parsePublic bytes = some pub) : PublicOptionShape.canonical pub := by
  cases hd : decode bytes with
  | none => simp [parsePublic, hd] at h
  | some wire =>
      simp only [parsePublic, hd] at h
      change (if PublicOptionShape.check (toPublic wire) = true
        then some (toPublic wire) else none) = some pub at h
      split at h
      next hc =>
        have hp := Option.some.inj h
        exact hp ▸ (PublicOptionShape.check_eq_true_iff (toPublic wire)).mp hc
      next hc => contradiction

theorem toPublic_index_bound (wire : Wire) :
    (toPublic wire).nextPairIndex < 2^64 := by
  cases wire with
  | transfer c recipient => exact c.nextPairIndex.isLt
  | withdrawal c amount => exact c.nextPairIndex.isLt

#print axioms parsePublic_canonical
#print axioms toPublic_index_bound
end AspisR1.SemanticPublicWire
