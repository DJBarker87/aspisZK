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
abbrev AffCoordinate := (Fin 10 × Fin 1024) ⊕ (Fin 3 × Fin 1024 × Fin 4)

abbrev MaskCoordinate := EligibleCell ⊕ AffCoordinate

abbrev EligibleNoise (K : Type) [Field K] (F : Subfield K) := EligibleCell → F

/-- D4″, with the user's H1 correction: the three extension slots remain
G, H1 padding, D. `AffCoordinate` is the index type; the tape is its F-valued
coordinate vector, not a uniformly selected index. -/
abbrev AffTape (K : Type) [Field K] (F : Subfield K) := AffCoordinate → F

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

/-- Eligible masks and row-1023 balancing read only fixed semantic C1
cells and eligible noise. No affine-tape coordinate is read here. -/
def applyEligible (t : Trace K) (e : EligibleNoise K F) : Trace K :=
  fun c r => if c.val < 16 then
    balance 1023 (fun s => t c s + semanticNoise (Sum.elim e 0) c s) r
  else t c r

/-- Full-domain mask-only, G/H1-padding/D operations, preserving semantic
C1 cells exactly. H1 padding remains in this tape by the Z3 correction. -/
def applyAff (B : PackBasis F) (t : Trace K) (tape : AffTape K F) : Trace K :=
  let full : MaskTape K F := Sum.elim 0 tape
  fun c r =>
    if c.val < 16 then t c r
    else if h : c.val < 26 then maskOnlyColumns full ⟨c.val - 16, by omega⟩ r
    else if c.val = 26 then t c r + h1Padding B full r
    else if c.val = 27 then balance 0 (extensionRaw B full 0) r
    else dWord B full r

/-- The original tape is split without changing its coordinates or balances. -/
def applyMask (B : PackBasis F) (t : Trace K) (tape : MaskTape K F) : Trace K :=
  applyAff B (applyEligible t (fun cell => tape (.inl cell)))
    (fun cell => tape (.inr cell))

/-- The composition has the same cellwise behavior as the Z2 port. -/
theorem applyMask_eq_port (B : PackBasis F) (t : Trace K) (tape : MaskTape K F) :
    applyMask B t tape = fun c r =>
      if c.val < 16 then balance 1023 (fun s => t c s + semanticNoise tape c s) r
      else if h : c.val < 26 then maskOnlyColumns tape ⟨c.val - 16, by omega⟩ r
      else if c.val = 26 then t c r + h1Padding B tape r
      else if c.val = 27 then balance 0 (extensionRaw B tape 0) r
      else dWord B tape r := by
  funext c r
  simp only [applyMask, applyAff, applyEligible, semanticNoise, maskOnlyColumns,
    h1Padding, extensionRaw, dWord, Sum.elim_inl, Sum.elim_inr]
  split_ifs <;> rfl

/-- Affinity over F in the remaining tape, for every fixed semantic trace.
The row-1023 balance is already in `applyEligible`, not in this operation. -/
theorem applyAff_affine (B : PackBasis F) (t : Trace K)
    (p q : AffTape K F) (a : F) :
    applyAff B t (a • p + (1 - a) • q) =
      a • applyAff B t p + (1 - a) • applyAff B t q := by
  classical
  let p' : MaskTape K F := Sum.elim 0 p
  let q' : MaskTape K F := Sum.elim 0 q
  have join : (Sum.elim 0 (a • p + (1 - a) • q) : MaskTape K F) =
      a • p' + (1 - a) • q' := by
    funext coord
    cases coord <;> simp [p', q', Pi.smul_apply, smul_eq_mul]
  have raw (coord : MaskCoordinate) :
      ((a • p' + (1 - a) • q') coord : K) =
        (a : K) * (p' coord : K) + (1 - (a : K)) * (q' coord : K) := by
    simp [Pi.smul_apply, smul_eq_mul]
  have ext (lane : Fin 3) (r : Fin 1024) :
      extensionRaw B (a • p' + (1 - a) • q') lane r =
        (a : K) * extensionRaw B p' lane r + (1 - (a : K)) * extensionRaw B q' lane r := by
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
      h1Padding B (a • p' + (1 - a) • q') r =
        (a : K) * h1Padding B p' r + (1 - (a : K)) * h1Padding B q' r := by
    unfold h1Padding
    have eq : (fun s => if CopyActiveRow s then 0 else
        extensionRaw B (a • p' + (1 - a) • q') 1 s) =
        (fun s => (a : K) * (if CopyActiveRow s then 0 else extensionRaw B p' 1 s) +
          (1 - (a : K)) * (if CopyActiveRow s then 0 else extensionRaw B q' 1 s)) := by
      funext s
      split_ifs
      · ring
      · exact ext 1 s
    rw [eq, bal]
  funext c r
  change applyAff B t (a • p + (1 - a) • q) c r =
    (a : K) * applyAff B t p c r + (1 - (a : K)) * applyAff B t q c r
  unfold applyAff
  rw [join]
  split_ifs
  · ring
  · unfold maskOnlyColumns maskOnlyRaw
    simp only [raw]
    exact bal _ _ _ _
  · rw [pad]
    ring
  · rw [show extensionRaw B (a • p' + (1 - a) • q') 0 =
        (fun r => (a : K) * extensionRaw B p' 0 r +
          (1 - (a : K)) * extensionRaw B q' 0 r) from funext (ext 0)]
    exact bal _ _ _ _
  · unfold dWord
    rw [show extensionRaw B (a • p' + (1 - a) • q') 2 =
        (fun r => (a : K) * extensionRaw B p' 2 r +
          (1 - (a : K)) * extensionRaw B q' 2 r) from funext (ext 2)]
    exact bal _ _ _ _

/-- A base-coordinate read, embedded in the extension field. -/
def readAff (coord : AffCoordinate) : AffTape K F →ₗ[F] K where
  toFun r := r coord
  map_add' p q := by simp
  map_smul' a p := by
    change ((a * p coord : F) : K) = (a : K) * (p coord : K)
    exact map_mul F.subtype a (p coord)

/-- Tower packing is a linear operation on the four base coordinates. -/
def extensionAff (B : PackBasis F) (lane : Fin 3) (r : Fin 1024) :
    AffTape K F →ₗ[F] K :=
  readAff (.inr (lane, r, 0)) + B.i • readAff (.inr (lane, r, 1)) +
    B.u • readAff (.inr (lane, r, 2)) + (B.i * B.u) • readAff (.inr (lane, r, 3))

/-- Symbolic balancing of a family of linear maps. -/
def balanceAff (d : Fin 1024) (f : Fin 1024 → AffTape K F →ₗ[F] K)
    (r : Fin 1024) : AffTape K F →ₗ[F] K :=
  if r = d then -(∑ s ∈ copyInactiveRows.erase d, f s) else f r

/-- The linear part of the masked trace. -/
def traceLinear (B : PackBasis F) : AffTape K F →ₗ[F] Trace K :=
  LinearMap.pi fun c => LinearMap.pi fun r =>
    if c.val < 16 then 0
    else if h : c.val < 26 then
      balanceAff 0 (fun s => readAff (.inl (⟨c.val - 16, by omega⟩, s))) r
    else if c.val = 26 then
      balanceAff 0 (fun s => if CopyActiveRow s then 0 else extensionAff B 1 s) r
    else if c.val = 27 then balanceAff 0 (extensionAff B 0) r
    else balanceAff 0 (extensionAff B 2) r

/-- The surviving trace at zero affine tape. -/
def traceBase (t : Trace K) : Trace K :=
  fun c r => if c.val < 16 ∨ c.val = 26 then t c r else 0

attribute [local irreducible] copyInactiveRows

/-- A coordinate proof of the actual port, without a message-affinity premise. -/
theorem applyAff_eq_base_add (B : PackBasis F) (t : Trace K) (r : AffTape K F) :
    applyAff B t r = traceBase t + traceLinear B r := by
  have he (lane : Fin 3) (s : Fin 1024) :
      extensionAff B lane s r = extensionRaw B (Sum.elim 0 r) lane s := by
    simp only [extensionAff, readAff, extensionRaw, pack4, LinearMap.add_apply,
      LinearMap.smul_apply, LinearMap.coe_mk, AddHom.coe_mk, smul_eq_mul, Sum.elim_inr]
  have hb (d : Fin 1024) (f : Fin 1024 → AffTape K F →ₗ[F] K) (s : Fin 1024) :
      balanceAff d f s r = balance d (fun u => f u r) s := by
    simp only [balanceAff, balance]
    split_ifs <;> simp only [LinearMap.neg_apply, LinearMap.sum_apply]
  have hp (s : Fin 1024) :
      (if CopyActiveRow s then (0 : AffTape K F →ₗ[F] K) else extensionAff B 1 s) r =
        if CopyActiveRow s then 0 else extensionRaw B (Sum.elim 0 r) 1 s := by
    split_ifs <;> simp only [LinearMap.zero_apply, he]
  funext c s
  simp only [applyAff, traceBase, traceLinear, Pi.add_apply, LinearMap.pi_apply]
  split_ifs <;> simp_all only [hb, he, hp, LinearMap.zero_apply, add_zero, zero_add,
    maskOnlyColumns, maskOnlyRaw, readAff, LinearMap.coe_mk, AddHom.coe_mk,
    Sum.elim_inr, h1Padding, dWord, ite_apply, true_or, false_or, or_true,
    not_true_eq_false, not_false_eq_true]
  all_goals first | rfl | omega

/-- The actual masking operation packaged as an affine map. -/
def traceAffine (B : PackBasis F) (t : Trace K) : AffTape K F →ᵃ[F] Trace K :=
  AffineMap.const F (AffTape K F) (traceBase t) + (traceLinear B).toAffineMap

theorem traceAffine_apply (B : PackBasis F) (t : Trace K) (r : AffTape K F) :
    traceAffine B t r = applyAff B t r := (applyAff_eq_base_add B t r).symm

#print axioms eligible
#print axioms AffCoordinate
#print axioms MaskCoordinate
#print axioms EligibleNoise
#print axioms AffTape
#print axioms MaskTape
#print axioms semanticNoise
#print axioms extensionRaw
#print axioms balance
#print axioms maskOnlyColumns
#print axioms dWord
#print axioms h1Padding
#print axioms applyEligible
#print axioms applyAff
#print axioms applyMask
#print axioms applyMask_eq_port
#print axioms applyAff_affine
#print axioms applyAff_eq_base_add
#print axioms traceAffine_apply
end R0Z.MaskLayout
