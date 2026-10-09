import R0Z.MaskedProtocol

/-! Z2 literal mask layout at d2b7413259a75100db9d1c722d88932bfea28fb9.
F = crates/aspis-statement/src/pool_v1/pair_forest_hiding.rs;
P = that directory's pair_tree_profile.rs; H = pair_tree_hiding.rs;
M = crates/aspis-prover/src/state_only_hiding.rs;
E = crates/aspis-prover/src/state_only_entropy.rs.
Tape coordinates are in the C1 base subfield, including four coordinates for
each extension-field sample. Finite tape means are taken only symbolically.
Salts do not affect the trace and are not coordinates of this mask tape. -/
set_option autoImplicit false
noncomputable section
namespace R0Z.MaskLayout
open R0P
attribute [local instance] Classical.propDecidable

/-- F:54-75,204-214: 24 paths, four bases 1,5,9,13 per block. -/
def forestPathUsed (c r : Nat) : Prop :=
  ∃ level : Fin 24,
    let base := 912 + 16 * (level.val / 4) + 1 + 4 * (level.val % 4)
    (r = base ∧ c ≤ 8) ∨ r = base + 1

/-- H:289-334, P:223-265,343-354. This helper deliberately retains the
legacy path test in the translated value region, as does the Rust call. -/
def pairAuxUsed (c r : Nat) : Prop :=
  864 ≤ r ∧ r < 1024 ∧ c < 16 ∧
    ((∃ level : Fin 21,
        let base := 864 + 16 * (level.val / 4) + 1 + 2 * (level.val % 4)
        (r = base ∧ c ≤ 8) ∨ r = base + 1 ∨ (r = base ^^^ 12 ∧ c < 8)) ∨
      (∃ value : Fin 3,
        let base := 960 + 2 * value.val
        (r = base ∨ r = base + 1 ∨ r = base ^^^ 12) ∧ c ≤ 10) ∨
      (r = 966 ∧ c < 3) ∨ (r = 967 ∧ c < 2) ∨
      (r = 969 ∧ c ≤ 10) ∨ (r = 970 ∧ c < 10))

/-- F:221-253, H:23: only the 16 semantic columns are eligible for this
additive cell mask. The ten additional columns have a separate full tape. -/
def eligible (c : Fin 29) (r : Fin 1024) : Prop :=
  c.val < 16 ∧
    ((r.val < 912 ∧ 13 ≤ r.val % 16) ∨
      (912 ≤ r.val ∧ ¬ (if r.val < 1008 then forestPathUsed c.val r.val
        else pairAuxUsed c.val (r.val - 48))))

abbrev EligibleCell := {cell : Fin 29 × Fin 1024 // eligible cell.1 cell.2}

/-- Semantic cells, ten mask-only columns, then G/H1-padding/D limbs.
The independent inputs include overwritten dependent samples for C1,
mask-only, G and D, as in M:448-471 and E:656-673. Unused H1 samples
are harmless redundant ideal coordinates; only inactive nonzero rows enter. -/
abbrev MaskCoordinate := EligibleCell ⊕ ((Fin 10 × Fin 1024) ⊕ (Fin 3 × Fin 1024 × Fin 4))

abbrev MaskTape (K : Type) [Field K] (F : Subfield K) := MaskCoordinate → F

variable {K : Type} [Field K] {F : Subfield K}

/-- M:710-713: add a base-field sample at exactly an eligible cell. -/
def semanticNoise (tape : MaskTape K F) (c : Fin 29) (r : Fin 1024) : K :=
  if h : eligible c r then (tape (.inl ⟨(c, r), h⟩) : K) else 0

def maskOnlyRaw (tape : MaskTape K F) (c : Fin 10) (r : Fin 1024) : K :=
  tape (.inr (.inl (c, r)))

/-- M:460-471; E:656-657: QM31 samples use four M31 coordinates.
Index 0 is G, 1 is H1 padding, 2 is D. -/
def extensionRaw (B : PackBasis F) (tape : MaskTape K F) (lane : Fin 3)
    (r : Fin 1024) : K :=
  pack4 B (fun limb => tape (.inr (.inr (lane, r, limb))))

/-- M:169-196: replace one inactive coordinate with minus the sum of the
others. `copyInactiveRows` is the existing model's literal forest registry
(Copy.lean:238-246, CopyConstants.lean:30-31), never enumerated here. -/
def balance (dependent : Fin 1024) (word : Fin 1024 → K) (r : Fin 1024) : K :=
  if r = dependent then -(∑ s ∈ copyInactiveRows.erase dependent, word s) else word r

/-- M:448-458: first inactive row = 0. -/
def maskOnlyColumns (tape : MaskTape K F) (c : Fin 10) : Fin 1024 → K :=
  balance 0 (maskOnlyRaw tape c)

/-- E:634-674,703-715 and D3: initial lane 28, derived from its own
ideal tape coordinates. Hash expansion and source-seed dependence are FS
refinement obligations, not a premise of this field-tape definition. -/
def dWord (B : PackBasis F) (tape : MaskTape K F) : Fin 1024 → K :=
  balance 0 (extensionRaw B tape 2)

/-- M:465-472,297-302: padding is zero on copy-active rows. The dependent
row is overwritten by balance. H1 is constructed after lambda/chi; this
operation only applies its padding to the H1 table supplied in `t`. -/
def h1Padding (B : PackBasis F) (tape : MaskTape K F) : Fin 1024 → K :=
  balance 0 (fun r => if CopyActiveRow r then 0 else extensionRaw B tape 1 r)

/-- M:676-722,762-773: add at eligible cells, then balance each semantic
column at its last eligible inactive row (1023). F:221-253 and the literal
active masks give this same row for all 16 columns. Install the separately
balanced mask-only, G and D words; pad the supplied adaptive H1 table. -/
def applyMask (B : PackBasis F) (t : Trace K) (tape : MaskTape K F) : Trace K :=
  fun c r =>
    if c.val < 16 then balance 1023 (fun s => t c s + semanticNoise tape c s) r
    else if h : c.val < 26 then maskOnlyColumns tape ⟨c.val - 16, by omega⟩ r
    else if c.val = 26 then t c r + h1Padding B tape r
    else if c.val = 27 then balance 0 (extensionRaw B tape 0) r
    else dWord B tape r

/-- Affinity in the base-field tape for every fixed input trace. No honesty,
rank, mask-image or privacy premise is used. The symbolic sum lemma avoids
reducing the 1024-row inactive set. -/
theorem applyMask_affine (B : PackBasis F) (t : Trace K)
    (p q : MaskTape K F) (a : F) :
    applyMask B t (a • p + (1 - a) • q) =
      a • applyMask B t p + (1 - a) • applyMask B t q := by
  classical
  have raw (coord : MaskCoordinate) :
      ((a • p + (1 - a) • q) coord : K) =
        (a : K) * (p coord : K) + (1 - (a : K)) * (q coord : K) := by
    simp [Pi.smul_apply, smul_eq_mul]
  have sem (c : Fin 29) (r : Fin 1024) :
      semanticNoise (a • p + (1 - a) • q) c r =
        (a : K) * semanticNoise p c r + (1 - (a : K)) * semanticNoise q c r := by
    unfold semanticNoise
    split_ifs
    · exact raw _
    · ring
  have ext (lane : Fin 3) (r : Fin 1024) :
      extensionRaw B (a • p + (1 - a) • q) lane r =
        (a : K) * extensionRaw B p lane r + (1 - (a : K)) * extensionRaw B q lane r := by
    simp only [extensionRaw, pack4, raw]
    ring
  have bal (d : Fin 1024) (u v : Fin 1024 → K) (r : Fin 1024) :
      balance d (fun s => (a : K) * u s + (1 - (a : K)) * v s) r =
        (a : K) * balance d u r + (1 - (a : K)) * balance d v r := by
    unfold balance
    split_ifs
    · simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
      ring
    · rfl
  have pad (r : Fin 1024) :
      h1Padding B (a • p + (1 - a) • q) r =
        (a : K) * h1Padding B p r + (1 - (a : K)) * h1Padding B q r := by
    unfold h1Padding
    have eq : (fun s => if CopyActiveRow s then 0 else
        extensionRaw B (a • p + (1 - a) • q) 1 s) =
        (fun s => (a : K) * (if CopyActiveRow s then 0 else extensionRaw B p 1 s) +
          (1 - (a : K)) * (if CopyActiveRow s then 0 else extensionRaw B q 1 s)) := by
      funext s
      split_ifs
      · ring
      · exact ext 1 s
    rw [eq, bal]
  funext c r
  change applyMask B t (a • p + (1 - a) • q) c r =
    (a : K) * applyMask B t p c r + (1 - (a : K)) * applyMask B t q c r
  unfold applyMask
  split_ifs
  · have eq : (fun s => t c s + semanticNoise (a • p + (1 - a) • q) c s) =
        (fun s => (a : K) * (t c s + semanticNoise p c s) +
          (1 - (a : K)) * (t c s + semanticNoise q c s)) := by
      funext s
      rw [sem]
      ring
    rw [eq, bal]
  · unfold maskOnlyColumns maskOnlyRaw
    simp only [raw]
    exact bal _ _ _ _
  · rw [pad]
    ring
  · rw [show extensionRaw B (a • p + (1 - a) • q) 0 =
        (fun r => (a : K) * extensionRaw B p 0 r +
          (1 - (a : K)) * extensionRaw B q 0 r) from funext (ext 0)]
    exact bal _ _ _ _
  · unfold dWord
    rw [show extensionRaw B (a • p + (1 - a) • q) 2 =
        (fun r => (a : K) * extensionRaw B p 2 r +
          (1 - (a : K)) * extensionRaw B q 2 r) from funext (ext 2)]
    exact bal _ _ _ _

#print axioms eligible
#print axioms MaskCoordinate
#print axioms MaskTape
#print axioms semanticNoise
#print axioms extensionRaw
#print axioms balance
#print axioms maskOnlyColumns
#print axioms dWord
#print axioms h1Padding
#print axioms applyMask
#print axioms applyMask_affine
end R0Z.MaskLayout
