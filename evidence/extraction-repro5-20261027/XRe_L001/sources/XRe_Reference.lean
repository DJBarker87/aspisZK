import Std
set_option autoImplicit false
namespace XRe_Reference
abbrev Bytes := List UInt8
inductive CodecError where
  | length | nonCanonical
  deriving DecidableEq, Repr

def chunks (width : Nat) (xs : Bytes) : List Bytes :=
  (List.range (xs.length / width)).map fun i => (xs.drop (i * width)).take width

def le32 (xs : Bytes) : Nat :=
  (xs.take 4).foldr (fun b n => b.toNat + 256 * n) 0

def canonical (limbs : Nat) (xs : Bytes) : Bool :=
  (List.range limbs).all fun j => decide (le32 ((xs.drop (4*j)).take 4) < 2147483647)

def checkValues (xs : Bytes) : Except CodecError Unit :=
  if (chunks 16 xs).all (canonical 4) then .ok () else .error .nonCanonical

def expandRow (xs : Bytes) : Bytes := xs ++ List.replicate 16 0

def expandRows (rows : List Bytes) : Bytes := rows.flatMap expandRow

def expandValues (xs out : Bytes) : Except CodecError Unit × Bytes :=
  if xs.length % 16 ≠ 0 ∨ out.length ≠ 2 * xs.length then (.error .length, out)
  else (.ok (), expandRows (chunks 16 xs))

def echeckRow (k : Bool) (xs : Bytes) : Bool :=
  canonical 8 xs && (!k || (xs.drop 16).all (fun b => b == 0))

def echeck (xs : Bytes) (k : Bool) : Except CodecError Unit :=
  if (chunks 32 xs).all (echeckRow k) then .ok () else .error .nonCanonical

/-- The incomplete final chunk is ignored, as in the reference loop. -/
theorem checkValues_short (xs : Bytes) (h : xs.length < 16) :
    checkValues xs = .ok () := by
  simp [checkValues, chunks, Nat.div_eq_of_lt h]

/-- Failure preserves every byte of the original destination. -/
theorem expandValues_error_frame (xs out : Bytes)
    (h : xs.length % 16 ≠ 0 ∨ out.length ≠ 2 * xs.length) :
    expandValues xs out = (.error .length, out) := by
  simp [expandValues, h]

theorem chunk16_length (xs row : Bytes) (h : row ∈ chunks 16 xs) :
    row.length = 16 := by
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp h
  have bound : i < xs.length / 16 := List.mem_range.mp hi
  simp only [List.length_take, List.length_drop]
  omega

theorem expandRows_length (rows : List Bytes)
    (h : ∀ row ∈ rows, row.length = 16) :
    (expandRows rows).length = 32 * rows.length := by
  induction rows with
  | nil => rfl
  | cons row rows ih =>
    have first := h row (by simp)
    have rest : ∀ r ∈ rows, r.length = 16 := by
      intro r hr
      exact h r (by simp [hr])
    have tail := ih rest
    simp only [expandRows, List.flatMap_cons, List.length_append, expandRow,
      List.length_replicate, List.length_cons] at *
    omega

theorem expandValues_success_length (xs out : Bytes)
    (aligned : xs.length % 16 = 0) (size : out.length = 2 * xs.length) :
    (expandValues xs out).2.length = out.length := by
  have rows : ∀ row ∈ chunks 16 xs, row.length = 16 := chunk16_length xs
  have count := expandRows_length (chunks 16 xs) rows
  have divlaw := Nat.mod_add_div xs.length 16
  simp only [chunks, List.length_map, List.length_range] at count
  have good : ¬ (xs.length % 16 ≠ 0 ∨ out.length ≠ 2 * xs.length) := by
    simp [aligned, size]
  simp only [expandValues, if_neg good]
  omega

/-- The six scalar sources, after actual source indexing has selected a slot.
This model does not assert the missing release-carrier correspondence. -/
inductive Point where
  | claim0 | claim1 | claim2 | extra | before | y1
  deriving DecidableEq

def sourceScalar {K : Type} (values : Point → K) (point : Point) : K :=
  match point with
  | .claim0 => values .claim0
  | .claim1 => values .claim1
  | .claim2 => values .claim2
  | .extra => values .extra
  | .before => values .before
  | .y1 => values .y1

theorem scalar_selection {K : Type} (values : Point → K) (point : Point) :
    sourceScalar values point = values point := by
  cases point <;> rfl

/-- Stateful digest operations: no purity, independence or collision law. -/
structure DigestOps (S : Type) where
  call : S → List Bytes → Bytes × S

/-- Serialized fields before the checksum. Field encodings and their association
with release Prepared/Accumulator are separate, presently unproved obligations. -/
def checkpoint {S : Type} (D : DigestOps S) (state : S) (proof publicInput : Bytes)
    (body : Bytes → Bytes → Bytes) (domain : Bytes) : Bytes × S × List (List Bytes) :=
  let (proofDigest, s1) := D.call state [proof]
  let (publicDigest, s2) := D.call s1 [publicInput]
  let payload := body proofDigest publicDigest
  let (checksum, s3) := D.call s2 [domain, payload]
  (payload ++ checksum, s3, [[proof], [publicInput], [domain, payload]])

theorem checkpoint_query_count {S : Type} (D : DigestOps S) (state : S)
    (proof publicInput : Bytes) (body : Bytes → Bytes → Bytes) (domain : Bytes) :
    (checkpoint D state proof publicInput body domain).2.2.length = 3 := by
  rfl

#print axioms checkValues_short
#print axioms expandValues_error_frame
#print axioms chunk16_length
#print axioms expandRows_length
#print axioms expandValues_success_length
#print axioms scalar_selection
#print axioms checkpoint_query_count
end XRe_Reference
