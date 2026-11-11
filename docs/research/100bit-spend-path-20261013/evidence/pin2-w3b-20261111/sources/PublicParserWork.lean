import PublicPrimitiveDecoderWork

/-! Complete public parser work schedule. Option failure preserves the work
of the executed prefix. Every cursor primitive has a bound on arbitrary
input; trailing garbage is rejected by a single constructor test.

PIN2 (2026-11-11, W3b): `decodeAfter` reads the appended binding suffix
(pool[32], deployment_domain[32], has_destination, destination[32] iff 1)
before the trailing-byte test, exactly as `SemanticPublicWire.decodeAfter`.
`bytes32` charges a strict length scan plus one comparison and one subtype
constructor (the 32 bytes were already copied by the capped cursor).  The
work constants below are recomputed exactly from the bind chain; the old
values were 100282 / 110000 / 110000 / 110003 / 110260. -/
set_option autoImplicit false
namespace AspisR1.PublicParserWork
open PublicPrimitiveDecoderWork
open SemanticPublicWire (Common Wire Digest M31)
abbrev Result (A : Type) := Option A × Nat

def pure {A : Type} (a : A) : Result A := (some a, 1)
def bind {A B : Type} (x : Result A) (f : A → Result B) : Result B :=
  match x.1 with
  | none => (none, x.2 + 1)
  | some a => let y := f a; (y.1, x.2 + y.2 + 1)

theorem bind_value {A B : Type} (x : Result A) (f : A → Result B) :
    (bind x f).1 = x.1.bind (fun a => (f a).1) := by
  cases x with | mk o n => cases o <;> rfl

theorem bind_work {A B : Type} (x : Result A) (f : A → Result B)
    (a b : Nat) (hx : x.2 ≤ a) (hf : ∀ v, (f v).2 ≤ b) :
    (bind x f).2 ≤ a+b+1 := by
  cases h : x.1 with
  | none => simp only [bind, h]; omega
  | some v => have hv := hf v; simp only [bind, h]; omega

def expect (tag : Byte) (xs : List Byte) : Result (List Byte) :=
  (SemanticPublicWire.expect tag xs, 2)

def readDigest := PublicPrimitiveDecoderWork.read 32 digest
 def readField := PublicPrimitiveDecoderWork.read 4 field
 def readIndex := PublicPrimitiveDecoderWork.read 8 index
 def readFrontier := PublicPrimitiveDecoderWork.read 640 frontier

/-- PIN2: the 32-byte raw field decoder, with its work. -/
def bytes32 (xs : List Byte) : Option SemanticPublicWire.Bytes32 × Nat :=
  (SemanticPublicWire.decodeBytes32 xs, (length xs).2 + 2)

theorem bytes32_value (xs : List Byte) :
    (bytes32 xs).1 = SemanticPublicWire.decodeBytes32 xs := rfl

theorem bytes32_work (xs : List Byte) (h : xs.length ≤ 32) : (bytes32 xs).2 ≤ 35 := by
  simp only [bytes32, length_work]; omega

def readBytes32 := PublicPrimitiveDecoderWork.read 32 bytes32

/-- PIN2: `has_destination` (0 or 1), then 32 bytes iff it is 1. -/
def readDestination : List Byte → Result (Option SemanticPublicWire.Bytes32 × List Byte)
  | [] => (none, 1)
  | tag :: rest =>
    if tag = 0 then (some (none, rest), 2)
    else if tag = 1 then
      ((readBytes32 rest).1.map (fun p => (some p.1, p.2)), (readBytes32 rest).2 + 3)
    else (none, 3)

theorem readDigest_value (xs : List Byte) :
    (readDigest xs).1 = SemanticPublicWire.readDigest xs := by
  simp only [readDigest, read_value, digest_value, SemanticPublicWire.readDigest]
theorem readField_value (xs : List Byte) :
    (readField xs).1 = SemanticPublicWire.readField xs := by
  simp only [readField, read_value, field_value, SemanticPublicWire.readField]

theorem readIndex_value (xs : List Byte) :
    (readIndex xs).1 = SemanticPublicWire.readIndex xs := by
  simp only [readIndex, read_value, index_value, SemanticPublicWire.readIndex]
theorem readFrontier_value (xs : List Byte) :
    (readFrontier xs).1 = SemanticPublicWire.readFrontier xs := by
  simp only [readFrontier, read_value, frontier_value, SemanticPublicWire.readFrontier]

theorem readBytes32_value (xs : List Byte) :
    (readBytes32 xs).1 = SemanticPublicWire.readBytes32 xs := by
  simp only [readBytes32, read_value, bytes32_value, SemanticPublicWire.readBytes32]

theorem readDestination_value (xs : List Byte) :
    (readDestination xs).1 = SemanticPublicWire.readDestination xs := by
  cases xs with
  | nil => rfl
  | cons tag rest =>
    simp only [readDestination, SemanticPublicWire.readDestination]
    split
    · rfl
    · split
      · rw [readBytes32_value]
      · rfl

theorem readDigest_work (xs : List Byte) : (readDigest xs).2 ≤ 2325 :=
  read_work 32 2225 digest (fun bs _ => digest_work bs) xs
theorem readField_work (xs : List Byte) : (readField xs).2 ≤ 277 :=
  read_work 4 261 field field_work xs
theorem readIndex_work (xs : List Byte) : (readIndex xs).2 ≤ 1061 :=
  read_work 8 1033 index index_work xs
theorem readFrontier_work (xs : List Byte) : (readFrontier xs).2 ≤ 48445 :=
  read_work 640 46521 frontier (fun bs _ => frontier_work bs) xs
theorem readBytes32_work (xs : List Byte) : (readBytes32 xs).2 ≤ 135 :=
  read_work 32 35 bytes32 bytes32_work xs

theorem readDestination_work (xs : List Byte) : (readDestination xs).2 ≤ 138 := by
  cases xs with
  | nil => change 1 ≤ 138; omega
  | cons tag rest =>
    have hr := readBytes32_work rest
    simp only [readDestination]
    split
    · dsimp only; omega
    · split <;> dsimp only <;> omega

def decodeAfter (anchor nullifier : Digest) (asset : M31) (change : Digest)
    (xs : List Byte) : Result Common :=
  bind (readIndex xs) fun (index, rest) =>
  bind (readFrontier rest) fun (snapshot, rest) =>
  bind (readDigest rest) fun (root, rest) =>
  bind (readFrontier rest) fun (nextFrontier, rest) =>
  bind (readBytes32 rest) fun (pool, rest) =>
  bind (readBytes32 rest) fun (domain, rest) =>
  bind (readDestination rest) fun (destination, rest) =>
  (if rest.isEmpty then some ⟨anchor, nullifier, asset, change, index, snapshot, root, nextFrontier,
      pool, domain, destination⟩
    else none, 2)

theorem decodeAfter_value (a n : Digest) (asset : M31) (c : Digest) (xs : List Byte) :
    (decodeAfter a n asset c xs).1 = SemanticPublicWire.decodeAfter a n asset c xs := by
  simp only [decodeAfter, bind_value, readIndex_value, readFrontier_value,
    readDigest_value, readBytes32_value, readDestination_value, SemanticPublicWire.decodeAfter]
  rfl

theorem decodeAfter_work (a n : Digest) (asset : M31) (c : Digest) (xs : List Byte) :
    (decodeAfter a n asset c xs).2 ≤ 100693 := by
  apply bind_work _ _ 1061 99631 (readIndex_work xs)
  intro ⟨idx, rest⟩
  apply bind_work _ _ 48445 51185 (readFrontier_work rest)
  intro ⟨snap, rest⟩
  apply bind_work _ _ 2325 48859 (readDigest_work rest)
  intro ⟨root, rest⟩
  apply bind_work _ _ 48445 413 (readFrontier_work rest)
  intro ⟨fr, rest⟩
  apply bind_work _ _ 135 277 (readBytes32_work rest)
  intro ⟨pool, rest⟩
  apply bind_work _ _ 135 141 (readBytes32_work rest)
  intro ⟨domain, rest⟩
  apply bind_work _ _ 138 2 (readDestination_work rest)
  intro ⟨dest, rest⟩
  exact Nat.le_refl _

 def decodeTransfer (xs : List Byte) : Result Wire :=
  bind (readDigest xs) fun (anchor, rest) =>
  bind (readDigest rest) fun (nullifier, rest) =>
  bind (readField rest) fun (asset, rest) =>
  bind (expect 1 rest) fun rest =>
  bind (readDigest rest) fun (recipient, rest) =>
  bind (readDigest rest) fun (change, rest) =>
  bind (expect 0 rest) fun rest =>
  bind (decodeAfter anchor nullifier asset change rest) fun c => pure (.transfer c recipient)

 def decodeWithdrawal (xs : List Byte) : Result Wire :=
  bind (readDigest xs) fun (anchor, rest) =>
  bind (readDigest rest) fun (nullifier, rest) =>
  bind (readField rest) fun (asset, rest) =>
  bind (expect 0 rest) fun rest =>
  bind (readDigest rest) fun (change, rest) =>
  bind (expect 1 rest) fun rest =>
  bind (readField rest) fun (amount, rest) =>
  bind (decodeAfter anchor nullifier asset change rest) fun c => pure (.withdrawal c amount)

theorem decodeTransfer_value (xs : List Byte) :
    (decodeTransfer xs).1 = SemanticPublicWire.decodeTransfer xs := by
  simp only [decodeTransfer, bind_value, readDigest_value, readField_value,
    expect, decodeAfter_value, pure, SemanticPublicWire.decodeTransfer]
  rfl

theorem decodeWithdrawal_value (xs : List Byte) :
    (decodeWithdrawal xs).1 = SemanticPublicWire.decodeWithdrawal xs := by
  simp only [decodeWithdrawal, bind_value, readDigest_value, readField_value,
    expect, decodeAfter_value, pure, SemanticPublicWire.decodeWithdrawal]
  rfl

theorem decodeTransfer_work (xs : List Byte) : (decodeTransfer xs).2 ≤ 110283 := by
  apply bind_work _ _ 2325 107957 (readDigest_work xs)
  intro ⟨anchor, rest⟩
  dsimp only
  apply bind_work _ _ 2325 105631 (readDigest_work rest)
  intro ⟨nullifier, rest⟩
  dsimp only
  apply bind_work _ _ 277 105353 (readField_work rest)
  intro ⟨asset, rest⟩
  dsimp only
  apply bind_work _ _ 2 105350 (Nat.le_refl _)
  intro rest
  apply bind_work _ _ 2325 103024 (readDigest_work rest)
  intro ⟨recipient, rest⟩
  dsimp only
  apply bind_work _ _ 2325 100698 (readDigest_work rest)
  intro ⟨change, rest⟩
  dsimp only
  apply bind_work _ _ 2 100695 (Nat.le_refl _)
  intro rest
  apply bind_work _ _ 100693 1 (decodeAfter_work _ _ _ _ _)
  intro c
  exact Nat.le_refl _

theorem decodeWithdrawal_work (xs : List Byte) : (decodeWithdrawal xs).2 ≤ 108235 := by
  apply bind_work _ _ 2325 105909 (readDigest_work xs)
  intro ⟨anchor, rest⟩
  dsimp only
  apply bind_work _ _ 2325 103583 (readDigest_work rest)
  intro ⟨nullifier, rest⟩
  dsimp only
  apply bind_work _ _ 277 103305 (readField_work rest)
  intro ⟨asset, rest⟩
  dsimp only
  apply bind_work _ _ 2 103302 (Nat.le_refl _)
  intro rest
  apply bind_work _ _ 2325 100976 (readDigest_work rest)
  intro ⟨change, rest⟩
  dsimp only
  apply bind_work _ _ 2 100973 (Nat.le_refl _)
  intro rest
  apply bind_work _ _ 277 100695 (readField_work rest)
  intro ⟨amount, rest⟩
  dsimp only
  apply bind_work _ _ 100693 1 (decodeAfter_work _ _ _ _ _)
  intro c
  exact Nat.le_refl _

def decode : List Byte → Result Wire
  | [] => (none, 1)
  | tag :: rest =>
    if tag = 0 then let r := decodeTransfer rest; (r.1, r.2+2)
    else if tag = 1 then let r := decodeWithdrawal rest; (r.1, r.2+3)
    else (none, 3)

theorem decode_value (xs : List Byte) : (decode xs).1 = SemanticPublicWire.decode xs := by
  cases xs with
  | nil => rfl
  | cons tag rest =>
    simp only [decode, SemanticPublicWire.decode]
    split
    · exact decodeTransfer_value rest
    · split
      · exact decodeWithdrawal_value rest
      · rfl

theorem decode_work (xs : List Byte) : (decode xs).2 ≤ 110285 := by
  cases xs with
  | nil => change 1 ≤ 110285; omega
  | cons tag rest =>
    have ht := decodeTransfer_work rest
    have hw := decodeWithdrawal_work rest
    simp only [decode]
    split
    · dsimp only; omega
    · split <;> dsimp only <;> omega

def parsePublic (xs : List Byte) : Result (R0P.Public M31) :=
  bind (decode xs) fun wire =>
    let pub := SemanticPublicWire.toPublic wire
    (if PublicOptionShape.check pub then some pub else none, 256)

theorem parsePublic_value (xs : List Byte) :
    (parsePublic xs).1 = SemanticPublicWire.parsePublic xs := by
  simp only [parsePublic, bind_value, decode_value, SemanticPublicWire.parsePublic]
  rfl

theorem parsePublic_work (xs : List Byte) : (parsePublic xs).2 ≤ 110542 := by
  exact bind_work _ _ 110285 256 (decode_work xs) (fun _ => Nat.le_refl _)

/-- PIN2 budget check: the M10 stage budget consumed downstream is 110260
(`PublicParserAllocationM10.spec`, `CostedExtractorStagesM10.workConstant`).
The recomputed bound exceeds it by exactly 282; the withdrawal branch alone
stays inside it (108235 + 3 + 257 = 108495). -/
theorem parsePublic_bound_over_old_budget : 110542 = 110260 + 282 := rfl
theorem decodeWithdrawal_within_old_budget : 108235 + 3 + 256 + 1 ≤ 110260 := by decide

#print axioms decodeTransfer_work
#print axioms decodeWithdrawal_work
#print axioms decode_work
#print axioms parsePublic_value
#print axioms parsePublic_work

#print axioms bind_value
#print axioms bind_work
#print axioms readDigest_value
#print axioms readField_value
#print axioms readIndex_value
#print axioms readFrontier_value
#print axioms readDigest_work
#print axioms readField_work
#print axioms readIndex_work
#print axioms readFrontier_work
#print axioms bytes32_work
#print axioms readBytes32_value
#print axioms readBytes32_work
#print axioms readDestination_value
#print axioms readDestination_work
#print axioms decodeAfter_value
#print axioms decodeAfter_work
#print axioms decodeTransfer_value
#print axioms decodeWithdrawal_value
#print axioms decode_value
end AspisR1.PublicParserWork
