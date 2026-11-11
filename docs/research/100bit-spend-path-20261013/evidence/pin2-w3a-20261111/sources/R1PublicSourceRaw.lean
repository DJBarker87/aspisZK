import R1SemanticPublicWire

/-! A raw-u32 shadow of the serialized projection
of Rust `r0::Public`, with the actual field dimensions, canonical-limb guard,
and check order. This is handwritten source-facing semantics, NOT extracted
Rust. A separate source-refinement premise is required to use it for Rust.
Allocation failures and outer ASF8 parsing are outside this model.
PIN2 (2026-11-10): the appended pool/domain/destination bytes are modelled;
they carry no guard (raw 32-byte account values). Only successful source results will be transported.
PIN2 W3a (2026-11-11): the destination is a field of the withdrawal constructor,
not of `Common`, mirroring the source: `r0::Public::Withdrawal` carries
`destination_token_account` (copied by `withdrawal_public` as `Some`), and
`r0::Public::Transfer` has none (`private_public` sets `None`). The option shape
is therefore fixed by the constructor, like recipient/amount. -/
set_option autoImplicit false
namespace AspisR1.PublicSourceRaw

abbrev Byte := ExactLeafFieldCodec.Byte
abbrev Bytes := List Byte
abbrev Word := RetainedFieldByteCodec.RawWord
abbrev M31 := ExactLeafFieldCodec.M31Exact
abbrev Digest := Fin 8 → Word
abbrev Frontier := Fin 20 → Digest

structure Common where
  anchor : Digest
  nullifier : Digest
  assetId : Word
  change : Digest
  nextPairIndex : PublicIndexCodec.Index
  snapshotFrontier : Frontier
  nextRoot : Digest
  nextFrontier : Frontier
  /-- PIN2: appended binding bytes (no canonicity guard: raw account bytes). -/
  pool : SemanticPublicWire.Bytes32
  deploymentDomain : SemanticPublicWire.Bytes32

/-- Source constructors fix option shape (recipient, amount and, since PIN2,
destination), but not withdrawal nonzero. -/
inductive Public
  | transfer (common : Common) (recipient : Digest)
  | withdrawal (common : Common) (amount : Word) (destination : SemanticPublicWire.Bytes32)

def fieldCanonical (x : Word) : Prop := x.val < RetainedFieldByteCodec.m31Modulus

def commonCanonical (c : Common) : Prop :=
  (∀ i, fieldCanonical (c.anchor i)) ∧
  (∀ i, fieldCanonical (c.nullifier i)) ∧ fieldCanonical c.assetId ∧
  (∀ i, fieldCanonical (c.change i)) ∧
  (∀ l i, fieldCanonical (c.snapshotFrontier l i)) ∧
  (∀ i, fieldCanonical (c.nextRoot i)) ∧
  (∀ l i, fieldCanonical (c.nextFrontier l i))

def Canonical : Public → Prop
  | .transfer c recipient => commonCanonical c ∧ ∀ i, fieldCanonical (recipient i)
  | .withdrawal c amount _ => commonCanonical c ∧ fieldCanonical amount

instance (x : Word) : Decidable (fieldCanonical x) :=
  inferInstanceAs (Decidable (x.val < RetainedFieldByteCodec.m31Modulus))

instance (c : Common) : Decidable (commonCanonical c) := by
  unfold commonCanonical
  infer_instance

instance (p : Public) : Decidable (Canonical p) := by
  cases p <;> unfold Canonical <;> infer_instance

def mapField (x : Word) (h : fieldCanonical x) : M31 :=
  RetainedExactLimbCodec.m31ResidueEquiv ⟨x.val, h⟩

def mapCommon (c : Common) (h : commonCanonical c)
    (destination : Option SemanticPublicWire.Bytes32) : SemanticPublicWire.Common :=
  { anchor := fun i => mapField (c.anchor i) (h.1 i)
    nullifier := fun i => mapField (c.nullifier i) (h.2.1 i)
    assetId := mapField c.assetId h.2.2.1
    change := fun i => mapField (c.change i) (h.2.2.2.1 i)
    nextPairIndex := c.nextPairIndex
    snapshotFrontier := fun l i => mapField (c.snapshotFrontier l i) (h.2.2.2.2.1 l i)
    nextRoot := fun i => mapField (c.nextRoot i) (h.2.2.2.2.2.1 i)
    nextFrontier := fun l i => mapField (c.nextFrontier l i) (h.2.2.2.2.2.2 l i)
    pool := c.pool
    deploymentDomain := c.deploymentDomain
    destination := destination }

def mapPublic (p : Public) (h : Canonical p) : SemanticPublicWire.Wire :=
  match p with
  | .transfer c recipient =>
      .transfer (mapCommon c h.1 none) (fun i => mapField (recipient i) (h.2 i))
  | .withdrawal c amount destination =>
      .withdrawal (mapCommon c h.1 (some destination)) (mapField amount h.2)

/-- Executable guarded mapping; no invalid limb is silently reduced modulo P. -/
def toWire (p : Public) : Option SemanticPublicWire.Wire :=
  if h : Canonical p then some (mapPublic p h) else none

def rawField (x : M31) : Word :=
  RetainedFieldByteCodec.m31AsRawWord (RetainedExactLimbCodec.m31ResidueEquiv.symm x)

def rawDigest (d : SemanticPublicWire.Digest) : Digest := fun i => rawField (d i)

def rawFrontier (f : SemanticPublicWire.Frontier) : Frontier :=
  fun l => rawDigest (f l)

def rawCommon (c : SemanticPublicWire.Common) : Common :=
  { anchor := rawDigest c.anchor
    nullifier := rawDigest c.nullifier
    assetId := rawField c.assetId
    change := rawDigest c.change
    nextPairIndex := c.nextPairIndex
    snapshotFrontier := rawFrontier c.snapshotFrontier
    nextRoot := rawDigest c.nextRoot
    nextFrontier := rawFrontier c.nextFrontier
    pool := c.pool
    deploymentDomain := c.deploymentDomain }

/-- Filler for a withdrawal wire without a destination; such a wire is not
shape-canonical and no theorem transports it (see `WireDestinationShape`). -/
def zeroBytes32 : SemanticPublicWire.Bytes32 := ⟨List.replicate 32 0, by simp⟩

def rawPublic : SemanticPublicWire.Wire → Public
  | .transfer c recipient => .transfer (rawCommon c) (rawDigest recipient)
  | .withdrawal c amount =>
      .withdrawal (rawCommon c) (rawField amount) (c.destination.getD zeroBytes32)

/-- The destination option shape of a wire record (present iff withdrawal). -/
def WireDestinationShape : SemanticPublicWire.Wire → Prop
  | .transfer c _ => c.destination = none
  | .withdrawal c _ => c.destination.isSome = true

def wordBytes (x : Word) : Bytes := List.ofFn (RetainedFieldByteCodec.encodeWordLE x)

/-- Source `fields` loop: reject before appending each noncanonical u32. -/
def fields : List Word → Option Bytes
  | [] => some []
  | x :: xs =>
      if fieldCanonical x then (fields xs).map (fun tail => wordBytes x ++ tail)
      else none

def digestBytes (d : Digest) : Option Bytes := fields (List.ofFn d)

/-- The source visits frontier levels in array order, then their eight limbs. -/
def digests : List Digest → Option Bytes
  | [] => some []
  | d :: ds => do
      let head ← digestBytes d
      let tail ← digests ds
      pure (head ++ tail)

def frontierBytes (f : Frontier) : Option Bytes := digests (List.ofFn f)

def header (c : Common) : Option Bytes := do
  let anchor ← digestBytes c.anchor
  let nullifier ← digestBytes c.nullifier
  let asset ← fields [c.assetId]
  pure (anchor ++ nullifier ++ asset)

def afterBytes (c : Common) : Option Bytes := do
  let snapshot ← frontierBytes c.snapshotFrontier
  let root ← digestBytes c.nextRoot
  let next ← frontierBytes c.nextFrontier
  pure (PublicIndexListCodec.encode c.nextPairIndex ++ snapshot ++ root ++ next ++
    SemanticPublicWire.encodeBytes32 c.pool ++ SemanticPublicWire.encodeBytes32 c.deploymentDomain)

/-- Allocation-free successful-result model of the literal source serializer.
Every Option.none here represents its `Error::Public` guard; it is not an
Aeneas execution result and says nothing about panic/allocation traces. -/
def serialize : Public → Option Bytes
  | .transfer c recipient => do
      let hd ← header c
      let recipientBytes ← digestBytes recipient
      let change ← digestBytes c.change
      let after ← afterBytes c
      pure ([0] ++ hd ++ [1] ++ recipientBytes ++ change ++ [0] ++ after ++
        SemanticPublicWire.encodeDestination none)
  | .withdrawal c amount destination => do
      let hd ← header c
      let change ← digestBytes c.change
      let amountBytes ← fields [amount]
      let after ← afterBytes c
      pure ([1] ++ hd ++ [0] ++ change ++ [1] ++ amountBytes ++ after ++
        SemanticPublicWire.encodeDestination (some destination))

/-- Exactly the additional option-shape fact needed by the checked parser. -/
def NonzeroWithdrawal : Public → Prop
  | .transfer _ _ => True
  | .withdrawal _ amount _ => amount.val ≠ 0

/-- The destination the source constructors put in `SemanticPublic`:
`private_public` sets `None`, `withdrawal_public` sets
`Some(destination_token_account)`. -/
def destination : Public → Option SemanticPublicWire.Bytes32
  | .transfer _ _ => none
  | .withdrawal _ _ d => some d

/-- PIN2: the destination option shape (W2 introduced it as a premise). -/
def DestinationShape (p : Public) : Prop :=
  match p with
  | .transfer _ _ => destination p = none
  | .withdrawal _ _ _ => (destination p).isSome = true

/-- PIN2 W3a: discharged for every source value, by the constructor shape. -/
theorem destinationShape (p : Public) : DestinationShape p := by
  cases p <;> rfl

/-- The amount clause of the source payment validator, not its other guards. -/
def PaymentAmountGuard : Public → Prop
  | .transfer _ _ => True
  | .withdrawal _ amount _ => 0 < amount.val ∧ amount.val < 2^30

#print axioms destinationShape
#print axioms serialize
#print axioms toWire
end AspisR1.PublicSourceRaw
