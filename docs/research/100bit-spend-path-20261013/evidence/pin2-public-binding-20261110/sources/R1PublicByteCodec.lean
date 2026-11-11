import R1ExactLeafFieldCodec
import R1FixedWidthDecoder
import PublicOptionShape

/-! PIN2 (2026-11-10): the compositional public codec also carries the
binding suffix appended to `public_bytes`: `pool[32]`, `deployment_domain[32]`
and the optional `destination_token_account[32]` behind a 0/1 tag. -/
set_option autoImplicit false
namespace AspisR1.PublicByteCodec

open R0P AspisV8R15.ExactTowerBase

abbrev Byte := RetainedFieldByteCodec.Byte
abbrev Bytes := List Byte
abbrev BasePublic := Public M31Exact
abbrev U64 := Fin (2^64)
abbrev Frontier := Fin 20 → Digest M31Exact
/-- PIN2: a raw 32-byte field. -/
abbrev Bytes32 := { bytes : Bytes // bytes.length = 32 }

/-- PIN2: the records the encoder accepts: a u64 index and 32-byte binding fields. -/
def WireOK (pub : BasePublic) : Prop :=
  pub.nextPairIndex < 2^64 ∧ pub.pool.length = 32 ∧ pub.deploymentDomain.length = 32 ∧
    pub.destination.all (fun d => d.length == 32) = true

instance (pub : BasePublic) : Decidable (WireOK pub) := by
  unfold WireOK
  infer_instance

abbrev WirePublic := { pub : BasePublic // WireOK pub }

structure PrefixCodec (A : Type) where
  emit : A → Bytes
  parse : Bytes → Option (A × Bytes)

namespace PrefixCodec
variable {A B : Type}

structure Lawful (c : PrefixCodec A) : Prop where
  round : ∀ a rest, c.parse (c.emit a ++ rest) = some (a, rest)
  back : ∀ bytes a rest, c.parse bytes = some (a, rest) → c.emit a ++ rest = bytes

def fixed (n : Nat) (emit : A → Bytes) (decode : Bytes → Option A) : PrefixCodec A where
  emit := emit
  parse bytes := (decode (bytes.take n)).map fun a => (a, bytes.drop n)

def pair (c : PrefixCodec A) (d : PrefixCodec B) : PrefixCodec (A × B) where
  emit ab := c.emit ab.1 ++ d.emit ab.2
  parse bytes := do
    let (a, mid) ← c.parse bytes
    let (b, rest) ← d.parse mid
    pure ((a, b), rest)

def transport (e : A ≃ B) (c : PrefixCodec A) : PrefixCodec B where
  emit b := c.emit (e.symm b)
  parse bytes := (c.parse bytes).map fun ar => (e ar.1, ar.2)

def option (c : PrefixCodec A) : PrefixCodec (Option A) where
  emit
    | none => [0]
    | some a => 1 :: c.emit a
  parse
    | [] => none
    | tag :: tail =>
        if tag = 0 then some (none, tail)
        else if tag = 1 then (c.parse tail).map fun ar => (some ar.1, ar.2)
        else none

end PrefixCodec

def variantCodec : PrefixCodec Variant where
  emit
    | .privateTransfer => [0]
    | .withdrawal => [1]
  parse
    | [] => none
    | tag :: tail =>
        if tag = 0 then some (.privateTransfer, tail)
        else if tag = 1 then some (.withdrawal, tail)
        else none

def encodeU32 (x : RetainedFieldByteCodec.RawWord) : Bytes :=
  List.ofFn (RetainedFieldByteCodec.encodeWordLE x)

def decodeU32 (bytes : Bytes) : Option RetainedFieldByteCodec.RawWord :=
  (RetainedFieldByteCodec.fixedBytes? 4 bytes).map RetainedFieldByteCodec.decodeWordLE

def u32Codec : PrefixCodec RetainedFieldByteCodec.RawWord :=
  PrefixCodec.fixed 4 encodeU32 decodeU32

-- First component is low u32; second component is high u32.
def u64Equiv :
    (RetainedFieldByteCodec.RawWord × RetainedFieldByteCodec.RawWord) ≃ U64 where
  toFun p := ⟨p.1.val + RetainedFieldByteCodec.rawWordCount * p.2.val, by
    have h0 := p.1.isLt
    have h1 := p.2.isLt
    norm_num [RetainedFieldByteCodec.rawWordCount] at *
    omega⟩
  invFun n :=
    (⟨n.val % RetainedFieldByteCodec.rawWordCount,
      Nat.mod_lt _ (by norm_num [RetainedFieldByteCodec.rawWordCount])⟩,
     ⟨n.val / RetainedFieldByteCodec.rawWordCount, by
       have hn := n.isLt
       norm_num [RetainedFieldByteCodec.rawWordCount] at *
       omega⟩)
  left_inv := by
    rintro ⟨lo, hi⟩
    have hlo := lo.isLt
    have hhi := hi.isLt
    apply Prod.ext
    · apply Fin.ext
      change (lo.val + RetainedFieldByteCodec.rawWordCount * hi.val) %
        RetainedFieldByteCodec.rawWordCount = lo.val
      norm_num [RetainedFieldByteCodec.rawWordCount] at *
      omega
    · apply Fin.ext
      change (lo.val + RetainedFieldByteCodec.rawWordCount * hi.val) /
        RetainedFieldByteCodec.rawWordCount = hi.val
      norm_num [RetainedFieldByteCodec.rawWordCount] at *
      omega
  right_inv := by
    intro n
    apply Fin.ext
    change n.val % RetainedFieldByteCodec.rawWordCount +
      RetainedFieldByteCodec.rawWordCount * (n.val / RetainedFieldByteCodec.rawWordCount) = n.val
    exact Nat.mod_add_div _ _

def u64Codec : PrefixCodec U64 :=
  PrefixCodec.transport u64Equiv (PrefixCodec.pair u32Codec u32Codec)

def m31Codec : PrefixCodec M31Exact :=
  PrefixCodec.fixed 4 ExactLeafFieldCodec.encodeM31 ExactLeafFieldCodec.decodeM31

def encodeDigest (d : Digest M31Exact) : Bytes :=
  FixedWidthDecoder.encode ExactLeafFieldCodec.encodeM31 d

def decodeDigest (bytes : Bytes) : Option (Digest M31Exact) :=
  FixedWidthDecoder.decode ExactLeafFieldCodec.decodeM31 4 8 bytes

def digestCodec : PrefixCodec (Digest M31Exact) :=
  PrefixCodec.fixed 32 encodeDigest decodeDigest

def encodeFrontier (f : Frontier) : Bytes := FixedWidthDecoder.encode encodeDigest f

def decodeFrontier (bytes : Bytes) : Option Frontier :=
  FixedWidthDecoder.decode decodeDigest 32 20 bytes

def frontierCodec : PrefixCodec Frontier :=
  PrefixCodec.fixed 640 encodeFrontier decodeFrontier

def decodeBytes32 (bytes : Bytes) : Option Bytes32 :=
  if h : bytes.length = 32 then some ⟨bytes, h⟩ else none

def bytes32Codec : PrefixCodec Bytes32 :=
  PrefixCodec.fixed 32 Subtype.val decodeBytes32

/-- PIN2: the destination with its length proof. -/
def destOf : (d : Option Bytes) → d.all (fun x => x.length == 32) = true → Option Bytes32
  | none, _ => none
  | some x, h => some ⟨x, by simpa using h⟩

theorem destOf_map_val (d : Option Bytes32) (h) : destOf (d.map Subtype.val) h = d := by
  cases d <;> rfl

theorem map_val_destOf (d : Option Bytes) (h) : (destOf d h).map Subtype.val = d := by
  cases d <;> rfl

theorem all_map_val (d : Option Bytes32) :
    (d.map Subtype.val).all (fun x => x.length == 32) = true := by
  cases d with
  | none => rfl
  | some b => simp [b.property]

-- Exactly the R0P.Public declaration order, with the Nat index bounded to u64
-- and (PIN2) the binding byte fields carrying their 32-byte lengths.
abbrev Fields :=
  Variant × Digest M31Exact × Digest M31Exact × M31Exact ×
    Option (Digest M31Exact) × Digest M31Exact × Option M31Exact × U64 ×
    Frontier × Digest M31Exact × Frontier × Bytes32 × Bytes32 × Option Bytes32

def toFields (p : WirePublic) : Fields :=
  ⟨p.val.variant, p.val.anchor, p.val.nullifier, p.val.assetId,
    p.val.recipient, p.val.change, p.val.withdrawalAmount,
    ⟨p.val.nextPairIndex, p.property.1⟩, p.val.snapshotFrontier,
    p.val.nextRoot, p.val.nextFrontier, ⟨p.val.pool, p.property.2.1⟩,
    ⟨p.val.deploymentDomain, p.property.2.2.1⟩, destOf p.val.destination p.property.2.2.2⟩

def fromFields : Fields → WirePublic
  | ⟨variant, anchor, nullifier, assetId, recipient, change, amount,
      index, frontier, root, next, pool, domain, destination⟩ =>
      ⟨{ variant := variant, anchor := anchor, nullifier := nullifier,
          assetId := assetId, recipient := recipient, change := change,
          withdrawalAmount := amount, nextPairIndex := index.val,
          snapshotFrontier := frontier, nextRoot := root, nextFrontier := next,
          pool := pool.val, deploymentDomain := domain.val,
          destination := destination.map Subtype.val },
        ⟨index.isLt, pool.property, domain.property, all_map_val destination⟩⟩

def publicFieldsEquiv : WirePublic ≃ Fields where
  toFun := toFields
  invFun := fromFields
  left_inv := by
    rintro ⟨⟨v, a, n, asset, recipient, change, amount, index, frontier, root, next,
      pool, domain, destination⟩, hp⟩
    cases destination <;> rfl
  right_inv := by
    rintro ⟨v, a, n, asset, recipient, change, amount, index, frontier, root, next,
      pool, domain, destination⟩
    cases destination <;> rfl

def fieldsCodec : PrefixCodec Fields :=
  PrefixCodec.pair variantCodec <|
  PrefixCodec.pair digestCodec <|
  PrefixCodec.pair digestCodec <|
  PrefixCodec.pair m31Codec <|
  PrefixCodec.pair (PrefixCodec.option digestCodec) <|
  PrefixCodec.pair digestCodec <|
  PrefixCodec.pair (PrefixCodec.option m31Codec) <|
  PrefixCodec.pair u64Codec <|
  PrefixCodec.pair frontierCodec <|
  PrefixCodec.pair digestCodec <|
  PrefixCodec.pair frontierCodec <|
  PrefixCodec.pair bytes32Codec <|
  PrefixCodec.pair bytes32Codec (PrefixCodec.option bytes32Codec)

def publicCodec : PrefixCodec WirePublic :=
  PrefixCodec.transport publicFieldsEquiv.symm fieldsCodec

def encode (pub : BasePublic) : Option Bytes :=
  if h : WireOK pub then some (publicCodec.emit ⟨pub, h⟩) else none

def parseRaw (bytes : Bytes) : Option BasePublic := do
  let (pub, rest) ← publicCodec.parse bytes
  if rest = [] then some pub.val else none

def decode (bytes : Bytes) : Option BasePublic := do
  let pub ← parseRaw bytes
  if PublicOptionShape.check pub = true then some pub else none

end AspisR1.PublicByteCodec
