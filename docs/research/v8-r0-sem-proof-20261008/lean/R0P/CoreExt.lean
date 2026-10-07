import R0P.Core

/-! # Skeleton extension (lead decisions after G3/G4)

* **Challenge-dependent families** (G4 finding): the copy residual reads the
  H1 helper at the current row (`A 26 b`) and the challenges λ, χ.
  `CFamily` carries them; `CHolds` fixes λ, χ and quantifies over rows.
* **Base typing and packing** (G3 finding): the Poseidon relation is the
  *unpacked* canonical permutation per base limb.  The source's packed
  terminal `v0 + i·v1 + u·v2 + i·u·v3` agrees with it on base-typed cells when
  `{1, i, u, i·u}` is linearly independent over the base subfield
  (`PackBasis`).  That the optimized raw-limb code computes the canonical
  permutation is a source-refinement obligation, not proved here. -/
set_option autoImplicit false
namespace R0P

variable {K : Type} [Field K]

/-- A family whose residuals read the H1 helper and the challenges λ, χ. -/
structure CFamily (K : Type) where
  residuals : Public K → (lam chi : K) → Openings K → (h1 : K) → Sel K → List K

def CHolds (f : CFamily K) (pub : Public K) (lam chi : K) (A : Trace K) : Prop :=
  ∀ b : Fin 1024, ∀ r ∈ f.residuals pub lam chi (rowOpenings A b) (A 26 b) (rowSel b), r = 0

/-- C1 columns 0–25 take values in the base subfield (Q11). -/
def BaseTyped (F : Subfield K) (A : Trace K) : Prop :=
  ∀ c : Fin 29, c.val < 26 → ∀ b, A c b ∈ F

/-- The packing basis `{1, i, u, i·u}` is independent over the base subfield. -/
structure PackBasis (F : Subfield K) where
  i : K
  u : K
  indep : ∀ a b c d : K, a ∈ F → b ∈ F → c ∈ F → d ∈ F →
    a + i * b + u * c + i * u * d = 0 → a = 0 ∧ b = 0 ∧ c = 0 ∧ d = 0

/-- The source's `qm31_pack_base4`. -/
def pack4 {F : Subfield K} (B : PackBasis F) (v : Fin 4 → K) : K :=
  v 0 + B.i * v 1 + B.u * v 2 + B.i * B.u * v 3

theorem pack4_eq_zero_iff {F : Subfield K} (B : PackBasis F) (v : Fin 4 → K)
    (hv : ∀ j, v j ∈ F) : pack4 B v = 0 ↔ ∀ j, v j = 0 := by
  constructor
  · intro h j
    obtain ⟨h0, h1, h2, h3⟩ := B.indep _ _ _ _ (hv 0) (hv 1) (hv 2) (hv 3) h
    fin_cases j <;> assumption
  · intro h
    simp [pack4, h]

#print axioms pack4_eq_zero_iff
end R0P
