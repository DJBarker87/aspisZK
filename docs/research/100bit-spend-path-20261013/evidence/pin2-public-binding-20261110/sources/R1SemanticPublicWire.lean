import R1PublicFieldBlockCodec
import R1PublicIndexListCodec
import R1PublicByteCursor
import PublicOptionShape

/-! Executable model of the source's section-9 semantic-public layout.
The ASF8 envelope, account binding, and Rust refinement are separate.
This wire carrier fixes the two variants' option shape and bounds the index
to its eight-byte representation; withdrawal nonzero is checked separately.

PIN2 (2026-11-10): after the next frontier, `public_bytes` appends
`pool[32]`, `deployment_domain[32]`, `has_destination` (one byte, 0 or 1) and,
iff `has_destination = 1`, `destination_token_account[32]`.  `decodeAfter`
reads that suffix before rejecting trailing bytes; the option check requires
the destination to be present exactly for a withdrawal. -/
set_option autoImplicit false
namespace AspisR1.SemanticPublicWire

abbrev Byte := ExactLeafFieldCodec.Byte
abbrev M31 := ExactLeafFieldCodec.M31Exact
abbrev Digest := PublicFieldBlockCodec.Digest
abbrev Frontier := PublicFieldBlockCodec.Frontier
/-- A raw 32-byte field (Solana account key or domain); no value constraint. -/
abbrev Bytes32 := { bytes : List Byte // bytes.length = 32 }

structure Common where
  anchor : Digest
  nullifier : Digest
  assetId : M31
  change : Digest
  nextPairIndex : PublicIndexCodec.Index
  snapshotFrontier : Frontier
  nextRoot : Digest
  nextFrontier : Frontier
  pool : Bytes32
  deploymentDomain : Bytes32
  destination : Option Bytes32

inductive Wire
  | transfer (common : Common) (recipient : Digest)
  | withdrawal (common : Common) (amount : M31)

def toPublic : Wire → R0P.Public M31
  | .transfer c recipient =>
      ⟨.privateTransfer, c.anchor, c.nullifier, c.assetId, some recipient,
        c.change, none, c.nextPairIndex.val, c.snapshotFrontier, c.nextRoot, c.nextFrontier,
        c.pool.val, c.deploymentDomain.val, c.destination.map Subtype.val⟩
  | .withdrawal c amount =>
      ⟨.withdrawal, c.anchor, c.nullifier, c.assetId, none,
        c.change, some amount, c.nextPairIndex.val, c.snapshotFrontier, c.nextRoot, c.nextFrontier,
        c.pool.val, c.deploymentDomain.val, c.destination.map Subtype.val⟩

def header (c : Common) : List Byte :=
  PublicFieldBlockCodec.encodeDigest c.anchor ++
    PublicFieldBlockCodec.encodeDigest c.nullifier ++ ExactLeafFieldCodec.encodeM31 c.assetId

def encodeBytes32 (b : Bytes32) : List Byte := b.val

def decodeBytes32 (bytes : List Byte) : Option Bytes32 :=
  if h : bytes.length = 32 then some ⟨bytes, h⟩ else none

def encodeDestination : Option Bytes32 → List Byte
  | none => [0]
  | some d => 1 :: encodeBytes32 d

/-- The PIN2 binding suffix. -/
def bindingBytes (c : Common) : List Byte :=
  encodeBytes32 c.pool ++ encodeBytes32 c.deploymentDomain ++ encodeDestination c.destination

def afterBytes (c : Common) : List Byte :=
  PublicIndexListCodec.encode c.nextPairIndex ++
    PublicFieldBlockCodec.encodeFrontier c.snapshotFrontier ++
    PublicFieldBlockCodec.encodeDigest c.nextRoot ++
    PublicFieldBlockCodec.encodeFrontier c.nextFrontier ++
    bindingBytes c

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
def readBytes32 := PublicByteCursor.read 32 decodeBytes32

/-- `has_destination` must be 0 (absent) or 1 (32 bytes follow). -/
def readDestination : List Byte → Option (Option Bytes32 × List Byte)
  | [] => none
  | tag :: rest =>
      if tag = 0 then some (none, rest)
      else if tag = 1 then (readBytes32 rest).map (fun p => (some p.1, p.2))
      else none

/-- Read the common suffix, including the PIN2 binding fields, and reject
trailing bytes. -/
def decodeAfter (anchor nullifier : Digest) (assetId : M31) (change : Digest)
    (bytes : List Byte) : Option Common := do
  let (index, rest) ← readIndex bytes
  let (snapshot, rest) ← readFrontier rest
  let (root, rest) ← readDigest rest
  let (frontier, rest) ← readFrontier rest
  let (pool, rest) ← readBytes32 rest
  let (domain, rest) ← readBytes32 rest
  let (destination, rest) ← readDestination rest
  if rest.isEmpty then
    some ⟨anchor, nullifier, assetId, change, index, snapshot, root, frontier,
      pool, domain, destination⟩
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

theorem encodeBytes32_length (b : Bytes32) : (encodeBytes32 b).length = 32 := b.property

theorem decodeBytes32_encodeBytes32 (b : Bytes32) :
    decodeBytes32 (encodeBytes32 b) = some b := by
  simp [decodeBytes32, encodeBytes32, b.property]

theorem encodeBytes32_of_decodeBytes32 (bytes : List Byte) (b : Bytes32)
    (h : decodeBytes32 bytes = some b) : encodeBytes32 b = bytes := by
  unfold decodeBytes32 at h
  split at h
  next hl =>
    cases h
    rfl
  next => contradiction

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

/-- PIN2: the parsed binding fields are the wire carrier's bytes. -/
theorem toPublic_binding (wire : Wire) :
    ∃ c : Common, (toPublic wire).pool = c.pool.val ∧
      (toPublic wire).deploymentDomain = c.deploymentDomain.val ∧
      (toPublic wire).destination = c.destination.map Subtype.val := by
  cases wire with
  | transfer c recipient => exact ⟨c, rfl, rfl, rfl⟩
  | withdrawal c amount => exact ⟨c, rfl, rfl, rfl⟩

#print axioms decodeBytes32_encodeBytes32
#print axioms encodeBytes32_of_decodeBytes32
#print axioms parsePublic_canonical
#print axioms toPublic_index_bound
#print axioms toPublic_binding
end AspisR1.SemanticPublicWire
