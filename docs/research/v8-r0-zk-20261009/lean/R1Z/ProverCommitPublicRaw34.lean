import Std

/-! Pure raw public serialization shared as identical source text by separate
Lean 4.31 and 4.32 checks. No Aeneas, M31 or algebra dependency. Separate checks
do not establish cross-version kernel integration or Rust runtime semantics. -/
set_option autoImplicit false
namespace AspisR1.PublicRawCore

abbrev Byte := Fin 256
abbrev Bytes := List Byte
abbrev Word := Fin (2 ^ 32)
abbrev Index := Fin (2 ^ 64)
abbrev Digest := Fin 8 → Word
abbrev Frontier := Fin 20 → Digest

def byteMod (n : Nat) : Byte := ⟨n % 256, Nat.mod_lt _ (by decide)⟩

/-- Exactly four little-endian bytes, enumerated by a sized function. -/
def wordByte (x : Word) (i : Fin 4) : Byte :=
  byteMod (x.val / 256 ^ i.val)

def wordBytes (x : Word) : Bytes := List.ofFn (wordByte x)

def lowWord (x : Index) : Word :=
  ⟨x.val % 2 ^ 32, Nat.mod_lt _ (Nat.two_pow_pos 32)⟩

def highWord (x : Index) : Word :=
  ⟨x.val / 2 ^ 32, by have hx := x.isLt; omega⟩

/-- Match the retained index codec's low-word/high-word split exactly. -/
def indexByte (x : Index) (i : Fin 8) : Byte :=
  if h : i.val < 4 then wordByte (lowWord x) ⟨i.val, h⟩
  else wordByte (highWord x) ⟨i.val - 4, by omega⟩

def indexBytes (x : Index) : Bytes := List.ofFn (indexByte x)

structure Common where
  anchor : Digest
  nullifier : Digest
  assetId : Word
  change : Digest
  nextPairIndex : Index
  snapshotFrontier : Frontier
  nextRoot : Digest
  nextFrontier : Frontier

inductive Public where
  | transfer : Common → Digest → Public
  | withdrawal : Common → Word → Public

def digestWords (d : Digest) : List Word := List.ofFn d

def frontierWords (f : Frontier) : List Word :=
  (List.ofFn f).flatMap digestWords

def headerWords (c : Common) : List Word :=
  digestWords c.anchor ++ digestWords c.nullifier ++ [c.assetId]

def afterWords (c : Common) : List Word :=
  frontierWords c.snapshotFrontier ++ digestWords c.nextRoot ++ frontierWords c.nextFrontier

/-- Serialized field words in source order; the U64 index is not an M31 word. -/
def words : Public → List Word
  | .transfer c recipient =>
    headerWords c ++ digestWords recipient ++ digestWords c.change ++ afterWords c
  | .withdrawal c amount =>
    headerWords c ++ digestWords c.change ++ [amount] ++ afterWords c

def Canonical (p : Public) : Prop := ∀ x ∈ words p, x.val < 2147483647

instance (p : Public) : Decidable (Canonical p) :=
  List.decidableBAll (fun x : Word => x.val < 2147483647) (words p)

def encodeWords (xs : List Word) : Bytes := xs.flatMap wordBytes

def afterBytes (c : Common) : Bytes :=
  indexBytes c.nextPairIndex ++ encodeWords (afterWords c)

/-- Total literal encoding; serialize adds the field-canonicality guard. -/
def encode : Public → Bytes
  | .transfer c recipient =>
    [0] ++ encodeWords (headerWords c) ++ [1] ++
      encodeWords (digestWords recipient) ++ encodeWords (digestWords c.change) ++
      [0] ++ afterBytes c
  | .withdrawal c amount =>
    [1] ++ encodeWords (headerWords c) ++ [0] ++ encodeWords (digestWords c.change) ++
      [1] ++ encodeWords [amount] ++ afterBytes c

def serialize (p : Public) : Option Bytes :=
  if Canonical p then some (encode p) else none

end AspisR1.PublicRawCore
