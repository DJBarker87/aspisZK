import R0Z.K4

/-! D49.4 C2: RF-dec (zf1/DESIGN-P-CERT.txt §1.2, §1.3, §2.3), Lean side.

The checker reads the challenge record as base-field limbs: each semantic row
is a WideExact value given by eight M31 limbs, and the query set is a list.
`decode` is the Lean decoder of that record, with the WideExact limb formula
of crates/aspis-core/src/field/wide_exact.rs:5-15
(`decode8(d) = decode4(d0..d3) + decode4(d4..d7)·v`,
`decode4(a,b,c,d) = (a + b·i) + (c + d·i)·u = pack4`).

* `decode_queries` (RF-dec, queries): the decoded query set is the list's
  `toFinset` — the premise `rf_dec` of `CertR1.queryCard_of_cert`.
* `decode_alpha` (RF-dec, α): `alpha` of the decoded record is the decoded
  semantic row `15 + j`; in particular α₉ is row 24.
* `decode_semK4` (RF-dec, sem): if limbs 4..7 of every semantic row vanish
  (the §1.2 check), every decoded semantic challenge lies in `K₄` — the
  body of `PredicateR1.SemK4`.

The identification of the Rust byte stream with `RawChallenges` (limb order,
canonicality) is the C3 extraction job. -/

set_option autoImplicit false

noncomputable section

namespace R1Z.RfDec

open R0P R0Z.HonestView R0Z.K4

variable {K : Type} [Field K] [Fintype K] {F : Subfield K}

/-- Lower QM31 half of eight WideExact limbs (limbs 0..3). -/
def lo (l : Fin 8 → F) : Fin 4 → K := fun k => (l (Fin.castAdd 4 k) : K)

/-- Upper QM31 half of eight WideExact limbs (limbs 4..7). -/
def hi (l : Fin 8 → F) : Fin 4 → K := fun k => (l (Fin.natAdd 4 k) : K)

/-- wide_exact.rs `decode8`, with `w` the Lean value of the generator `v`. -/
def wideDecode (B : PackBasis F) (w : K) (l : Fin 8 → F) : K :=
  pack4 B (lo l) + pack4 B (hi l) * w

/-- A WideExact value with zero upper limbs lies in `K₄`. -/
theorem wideDecode_mem_K4 (B : PackBasis F) (hB : PackField B) (w : K) (l : Fin 8 → F)
    (h : ∀ k : Fin 4, l (Fin.natAdd 4 k) = 0) : wideDecode B w l ∈ K4 B hB := by
  have hz (k : Fin 4) : hi l k = 0 := by
    simp only [hi, h k, ZeroMemClass.coe_zero]
  have hhi : pack4 B (hi l) = 0 := by
    unfold pack4
    rw [hz 0, hz 1, hz 2, hz 3]
    ring
  rw [wideDecode, hhi, zero_mul, add_zero]
  exact (mem_K4_iff_pack4 B hB).2 ⟨lo l, fun j => (l (Fin.castAdd 4 j)).2, rfl⟩

/-- The challenge record as the checker reads it.  The circle points and the
opening scalars are carried as field values: no `P_R1` decoder premise is
about them. -/
structure RawChallenges (K : Type) [Field K] (F : Subfield K) where
  sem : Fin 25 → Fin 8 → F
  circle : Fin 2 → AspisR0.ChordGeometry.Point K
  opening : Fin 4 → K
  queries : List (Fin 262144)

/-- The Lean decoder of the checker's challenge record. -/
def decode (B : PackBasis F) (w : K) (raw : RawChallenges K F) : Challenges K where
  sem := fun i => wideDecode B w (raw.sem i)
  circle := raw.circle
  opening := raw.opening
  queries := raw.queries.toFinset

theorem decode_queries (B : PackBasis F) (w : K) (raw : RawChallenges K F) :
    (decode B w raw).queries = raw.queries.toFinset := rfl

theorem decode_alpha (B : PackBasis F) (w : K) (raw : RawChallenges K F) (j : Fin 10) :
    alpha (decode B w raw) j = wideDecode B w (raw.sem ⟨15 + j.val, by omega⟩) := rfl

theorem decode_alpha_nine (B : PackBasis F) (w : K) (raw : RawChallenges K F) :
    alpha (decode B w raw) 9 = wideDecode B w (raw.sem 24) := rfl

theorem decode_semK4 (B : PackBasis F) (hB : PackField B) (w : K) (raw : RawChallenges K F)
    (h : ∀ (i : Fin 25) (k : Fin 4), raw.sem i (Fin.natAdd 4 k) = 0) :
    ∀ i : Fin 25, (decode B w raw).sem i ∈ K4 B hB :=
  fun i => wideDecode_mem_K4 B hB w (raw.sem i) (h i)

/-- Every decoded α lies in `K₄` under the same limb check. -/
theorem decode_alpha_mem_K4 (B : PackBasis F) (hB : PackField B) (w : K)
    (raw : RawChallenges K F)
    (h : ∀ (i : Fin 25) (k : Fin 4), raw.sem i (Fin.natAdd 4 k) = 0) (j : Fin 10) :
    alpha (decode B w raw) j ∈ K4 B hB :=
  decode_semK4 B hB w raw h _

#print axioms wideDecode_mem_K4
#print axioms decode_queries
#print axioms decode_alpha
#print axioms decode_alpha_nine
#print axioms decode_semK4
#print axioms decode_alpha_mem_K4

end R1Z.RfDec

end
