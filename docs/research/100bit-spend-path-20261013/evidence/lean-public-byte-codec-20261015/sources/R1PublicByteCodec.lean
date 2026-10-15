import R1ExactLeafFieldCodec
import R1FixedWidthDecoder
import PublicOptionShape

set_option autoImplicit false
namespace AspisR1.PublicByteCodec

open R0P AspisV8R15.ExactTowerBase

abbrev Byte := RetainedFieldByteCodec.Byte
abbrev Bytes := List Byte
abbrev BasePublic := Public M31Exact
abbrev U64 := Fin (2^64)
abbrev Frontier := Fin 20 → Digest M31Exact
abbrev WirePublic := { pub : BasePublic // pub.nextPairIndex < 2^64 }

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

-- Exactly the R0P.Public declaration order, with the Nat index bounded to u64.
abbrev Fields :=
  Variant × Digest M31Exact × Digest M31Exact × M31Exact ×
    Option (Digest M31Exact) × Digest M31Exact × Option M31Exact × U64 ×
    Frontier × Digest M31Exact × Frontier

def toFields (p : WirePublic) : Fields :=
  ⟨p.val.variant, p.val.anchor, p.val.nullifier, p.val.assetId,
    p.val.recipient, p.val.change, p.val.withdrawalAmount,
    ⟨p.val.nextPairIndex, p.property⟩, p.val.snapshotFrontier,
    p.val.nextRoot, p.val.nextFrontier⟩

def fromFields : Fields → WirePublic
  | ⟨variant, anchor, nullifier, assetId, recipient, change, amount,
      index, frontier, root, next⟩ =>
      ⟨{ variant := variant, anchor := anchor, nullifier := nullifier,
          assetId := assetId, recipient := recipient, change := change,
          withdrawalAmount := amount, nextPairIndex := index.val,
          snapshotFrontier := frontier, nextRoot := root, nextFrontier := next },
        index.isLt⟩

def publicFieldsEquiv : WirePublic ≃ Fields where
  toFun := toFields
  invFun := fromFields
  left_inv := by
    rintro ⟨p, hp⟩
    cases p
    rfl
  right_inv := by
    rintro ⟨v, a, n, asset, recipient, change, amount, index, frontier, root, next⟩
    rfl

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
  PrefixCodec.pair digestCodec frontierCodec

def publicCodec : PrefixCodec WirePublic :=
  PrefixCodec.transport publicFieldsEquiv.symm fieldsCodec

def encode (pub : BasePublic) : Option Bytes :=
  if h : pub.nextPairIndex < 2^64 then some (publicCodec.emit ⟨pub, h⟩) else none

def parseRaw (bytes : Bytes) : Option BasePublic := do
  let (pub, rest) ← publicCodec.parse bytes
  if rest = [] then some pub.val else none

def decode (bytes : Bytes) : Option BasePublic := do
  let pub ← parseRaw bytes
  if PublicOptionShape.check pub = true then some pub else none

end AspisR1.PublicByteCodec
