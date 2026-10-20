import WireBindingRecordCodec
import Mathlib.Data.List.OfFn

/-! Module of record for the binary commitment / typed R1 wire grammar.
The generic byte carrier admits both soundness's `Fin 256` and privacy's
`UInt8`. Binding classes reuse the D79 codec, including its checksum body;
there is no second copy of that codec or its separation proofs here.
Existing frozen definitions are identified in the two importing bridges. -/
set_option autoImplicit false
namespace AspisR1.SharedBinaryRecordGrammar

def nodeInput {Byte : Type} [OfNat Byte 18] (cs : Fin 2 → Fin 32 → Byte) : List Byte :=
  0x12 :: (List.ofFn (cs 0) ++ List.ofFn (cs 1))

def leafInput {Byte : Type} [OfNat Byte 16] (tag : Byte)
    (packed salt : List Byte) : List Byte := 0x10 :: tag :: (packed ++ salt)

def treeTag (t : Fin 3) : UInt8 :=
  if t.val = 0 then 0x71 else if t.val = 1 then 0xf1 else 0x72

def semanticSize (i : Fin 27) : Nat :=
  if i.val = 2 ∨ i.val = 14 then 32
  else if 15 ≤ i.val ∧ i.val ≤ 24 then 896
  else if i.val = 25 then 3712
  else if i.val = 26 then 928 else 0

def semanticTag (i : Fin 27) : UInt8 :=
  if i.val = 2 then 1 else if i.val = 14 then 3
  else if 15 ≤ i.val ∧ i.val ≤ 24 then 2
  else if i.val = 25 then 4 else if i.val = 26 then 5 else 0

def openingSize (i : Fin 4) : Nat :=
  if i.val = 0 then 928 else if i.val = 1 then 32 else if i.val = 2 then 224 else 256

def le32 (n : Nat) : List UInt8 :=
  [(n % 256).toUInt8, (n / 256 % 256).toUInt8, (n / 65536 % 256).toUInt8,
    (n / 16777216 % 256).toUInt8]

structure Wire where
  semantic : (i : Fin 27) → Vector UInt8 (semanticSize i)
  opening : (i : Fin 4) → Vector UInt8 (openingSize i)
  final : Vector UInt8 2048
  publicBytes : List UInt8
  tag : UInt8

def framed (w : Wire) (i : Fin 27) : List UInt8 :=
  [semanticTag i] ++ le32 (semanticSize i) ++ (w.semantic i).toList

abbrev BindingClass := WireBindingRecordCodec.BindingClass
abbrev BindingRecord := WireBindingRecordCodec.BindingRecord
abbrev CheckpointBody := WireBindingRecordCodec.CheckpointBody
abbrev Tx1Class := WireBindingRecordCodec.Tx1Class
abbrev classSize := WireBindingRecordCodec.Tx1Class.size
abbrev bindingSize := WireBindingRecordCodec.BindingClass.size
abbrev bindingBytes := WireBindingRecordCodec.BindingRecord.bytes

/-- Reuse the established typed-class separation result. -/
theorem class_safe (c : Tx1Class) (hn : c ≠ .binaryNode) :
    classSize c ≠ 65 ∧ classSize c ≠ 31 :=
  WireBindingRecordCodec.tx1_class_safe c hn

#print axioms class_safe
end AspisR1.SharedBinaryRecordGrammar
