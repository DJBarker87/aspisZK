import R1Z.CertRelWId
import R1Z.CertData

/-! D64 hRel (4), pure and at the CertData level (no Aeneas): **`rel_data`** — if the
relation matrix `rel` satisfies the CertRelK bridge `RelEntry` with the Rust coefficient
model `coefP` of abstract builder inputs (alpha `A`, OOD limbs `Z`, transport `T`, inverse
transport `TI`, inactive flags `Fl`, openings `κ, α₀, α₁`, quarter `Q`, half `H`, folded
positions `Fp`, relation kinds `rk`, queries `ru`, line inverses `L0, L1, L2`, stored
log-16 nodes `X`), then under the named premises on those inputs and the WideExact limb
basis `wb = wbP`, every relation limb functional `relMat` is `φ` of the matrix entry:
exactly the `hRel` hypothesis of `check_sound'''` for the rows `relRows rk ru`.  The
Aeneas side (CertRelFill `fill_rel_entries`) supplies `RelEntry` from the builder run. -/

set_option autoImplicit false

noncomputable section

namespace R1Z.CertRel

open scoped BigOperators
open R0P R0Z.HonestView R1Z.Batched R1Z.VerifierRelationsR1 R1Z.PredicateR1 R1Z.RfBat R1Z.CertData

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K] {F : Subfield K}

/-- The checker rows: relation `relOf (rk ρ) (ru ρ)`, limb `x mod 8`, for `ρ = x / 8`. -/
def relRows {q : ℕ} (rk ru : ℕ → ℕ) : Fin q → R1Rel × Fin 8 := fun x =>
  (relOf (rk (x.val / 8)) (ru (x.val / 8)), ⟨x.val % 8, Nat.mod_lt _ (by norm_num)⟩)

omit [Fintype K] [DecidableEq K] [Algebra (ZMod AspisCircleGroupOrder.P) K] in
theorem coefP_eq_M (nf : ℕ) (A2 A3 Q : K) (W2 : ℕ → K) (Fp : ℕ → ℕ) (LF NL : ℕ → K) (kd U i : ℕ) :
    coefP nf A2 A3 Q W2 Fp LF NL kd U i = coefM nf A2 A3 Q W2 Fp LF NL kd U i := by
  unfold coefP coefM
  split_ifs <;> rfl

/-- **`rel_data`**: the relation limb functionals are the entries of a `RelEntry` matrix. -/
theorem rel_data (π : Fin 1024 ≃ Fin 1024) (ch : Challenges K) (φ : ZP →+* ↥F) (i u w : K)
    (wb : Module.Basis (Fin 8) F K) (hwb : ∀ k : Fin 8, wb k = wbP i u w k.val)
    {nf : ℕ} (fp : Fin nf → Fin 262144) (hinj : Function.Injective fp) (Fp : ℕ → ℕ)
    (hFp : ∀ f : Fin nf, Fp f.val = (fp f).val)
    (A Z : ℕ → K) (T TI : ℕ → ℕ) (Fl : ℕ → K) (κ α0 α1 Q H : K)
    (hA : ∀ (j : ℕ) (h : j < 10), A j = alpha ch ⟨j, h⟩)
    (hZx : ∀ j : Fin 2, Z (2 * j.val) = (ch.circle j).1.1)
    (hZy : ∀ j : Fin 2, Z (2 * j.val + 1) = (ch.circle j).1.2)
    (hT : ∀ r : Fin 1024, T r.val = (π r).val)
    (hFl : ∀ r : Fin 1024, Fl r.val = if r ∈ copyInactiveRows then 1 else 0)
    (hTI : ∀ j : Fin 1024, TI j.val = (π.symm j).val)
    (hκ : κ = ch.opening 1) (hα0 : α0 = ch.opening 2) (hα1 : α1 = ch.opening 3)
    (hQ : Q = AspisR1.RoundPairing.quarter) (hH : H = 1 / 2)
    (rk ru : ℕ → ℕ) (L0 L1 L2 X : ℕ → K) {q bw : ℕ} (hbw : bw = (78 + nf) * 8)
    (hU1 : ∀ ρ, ru ρ < 262144)
    (hU2 : ∀ ρ, 8 * ρ < q → 3 ≤ rk ρ →
      (⟨ru ρ % 262144, Nat.mod_lt _ (by norm_num)⟩ : Fin 262144) ∈ ch.queries)
    (hL0 : ∀ ρ, 8 * ρ < q → 4 ≤ rk ρ → L0 ρ = algebraMap (ZMod AspisCircleGroupOrder.P) K
      (R1Z.BatchedAlgebra.lineInverse ⟨ru ρ / 4, by have := hU1 ρ; omega⟩ 0))
    (hL1 : ∀ ρ, 8 * ρ < q → 4 ≤ rk ρ → L1 ρ = algebraMap (ZMod AspisCircleGroupOrder.P) K
      (R1Z.BatchedAlgebra.lineInverse ⟨ru ρ / 4, by have := hU1 ρ; omega⟩ 1))
    (hL2 : ∀ ρ, 8 * ρ < q → 4 ≤ rk ρ → L2 ρ = algebraMap (ZMod AspisCircleGroupOrder.P) K
      (R1Z.BatchedAlgebra.lineInverse ⟨ru ρ / 4, by have := hU1 ρ; omega⟩ 2))
    (hX : ∀ ρ, 8 * ρ < q → 4 ≤ rk ρ → X ρ = algebraMap (ZMod AspisCircleGroupOrder.P) K
      (AspisV5FriReleasedLineGeometry.storedLine16X ⟨ru ρ / 4, by have := hU1 ρ; omega⟩))
    (rel : ℕ → ZP)
    (hent : RelEntry ((Subfield.subtype F).comp φ) i u w rel bw q (fun ρ c =>
      coefP nf α0 α1 Q (w2P A Z T TI Fl κ α0 α1 Q) Fp (lfvP H α1 (L0 ρ) (L1 ρ) (L2 ρ))
        (fun e => natP (X ρ) e 10) (rk ρ) (ru ρ) c)) :
    ∀ (x : Fin q) (c : Fin ((78 + nf) * 8)),
      relMat wb π ch fp (relRows rk ru) x c = φ (rowM rel bw x c) := by
  intro x c
  obtain ⟨⟨cell, m⟩, rfl⟩ := (fpb nf).surjective c
  rw [relMat_unit wb π ch fp hinj (relRows rk ru) x cell m]
  have hx := x.isLt
  have hρ : 8 * (x.val / 8) < q := by omega
  have hc : ((fpb nf) (cell, m)).val = m.val + 8 * cell.val := by
    simp only [fpb, finProdFinEquiv_apply_val]
  have hcm := m.isLt
  have h8 : (m.val + 8 * cell.val) / 8 = cell.val := by omega
  have h8' : (m.val + 8 * cell.val) % 8 = m.val := by omega
  obtain ⟨l, hl1, hl2⟩ := hent x.val ((fpb nf) (cell, m)).val hx (by rw [hbw]; exact ((fpb nf) (cell, m)).isLt)
  rw [hc, h8, h8'] at hl2
  beta_reduce at hl2
  have hW2 : ∀ e : Fin 64, w2P A Z T TI Fl κ α0 α1 Q e.val = w2 π ch e :=
    w2P_ident π ch A Z T TI Fl hA hZx hZy hT hFl hTI κ α0 α1 Q hκ hα0 hα1 hQ
  have hR := coefM_eq π ch fp Fp hFp α0 α1 Q hα0 hα1 hQ (w2P A Z T TI Fl κ α0 α1 Q) hW2
    (rk (x.val / 8)) (ru (x.val / 8)) (lfvP H α1 (L0 (x.val / 8)) (L1 (x.val / 8)) (L2 (x.val / 8)))
    (fun e => natP (X (x.val / 8)) e 10) (hU1 _) (hU2 _ hρ)
    (fun h4 t ht => by
      rw [lfvP_eq H α1 _ _ _ hH t ht, hL0 _ hρ h4, hL1 _ hρ h4, hL2 _ hρ h4])
    (fun h4 e he => by
      show natP (X (x.val / 8)) e 10 = _
      rw [natP_eq _ 10 e (by norm_num; omega), hX _ hρ h4]) cell
  rw [← coefP_eq_M] at hR
  show wb.repr (relR1 π ch (Pi.single (batCell fp cell) (1 : K) : R1Bat → K)
      (relOf (rk (x.val / 8)) (ru (x.val / 8))) * wb m) ⟨x.val % 8, Nat.mod_lt _ (by norm_num)⟩ = _
  have hs : ∑ k ∈ Finset.range 8, ((Subfield.subtype F).comp φ) (l k) * wbP i u w k =
      ∑ k : Fin 8, φ (l k.val) • wb k := by
    rw [← Fin.sum_univ_eq_sum_range (fun k => ((Subfield.subtype F).comp φ) (l k) * wbP i u w k) 8]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hwb k]
    rfl
  rw [← hR, hwb m, ← hl2, hs, Module.Basis.repr_sum_self]
  show φ (l (x.val % 8)) = φ (rel (x.val * bw + ((fpb nf) (cell, m)).val))
  rw [hl1]

#print axioms coefP_eq_M
#print axioms rel_data

end R1Z.CertRel

end
