import R1Z.CertCheckSound
import R1Z.CertRelData

/-! D64 hRel (5), the CertData-level composition (pure, no Aeneas import):
**`p_r1_of_data_rel`** is `p_r1_of_data` with the relation identification `hRel`
discharged by `rel_data` for the rows `relRows rk ru`: the relation matrix `d.rel` is a
CertRelK `RelEntry` matrix of the Rust coefficient model (`hent`, which the Aeneas
lemma `fill_rel_entries` gives for `d = toData pb ct` from the extracted `fill_rel` run),
and the model inputs satisfy the named premises (alpha, OOD, transport, inverse
transport, inactive flags, openings, M31 quarter and half, folded positions, relation
descriptors, line inverses, stored log-16 nodes) with the WideExact limb basis
`wb = wbP B.i B.u w`.

The pb/ct-level wrapper (`check_sound'''` with `hRel` replaced, importing CertCheckSound4)
exceeds -M7000 at import (attempts 4615, 4616), so the composition is stated here. -/

set_option autoImplicit false

noncomputable section

namespace R1Z.CertCheckSound

open scoped BigOperators
open R0P R0Z.MaskLayout R0Z.HonestView R0Z.Partition R0Z.K4
open R1Z.Batched R1Z.VerifierRelationsR1 R1Z.PredicateR1 R1Z.CertSound R1Z.CertR1
open R1Z.RfDec R1Z.RfSrc R1Z.RfChain R1Z.RfOwnLimb R1Z.RfBat R1Z.CertData R1Z.CertRel

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K] {F : Subfield K}

/-- **`p_r1_of_data_rel`**: `p_r1_of_data` without `hRel`. -/
theorem p_r1_of_data_rel (π : Fin 1024 ≃ Fin 1024) (B : PackBasis F) (hB : PackField B)
    (w : K) (raw : RawChallenges K F) (y : K) (d : CData) (hd : DataOK d) (φ : ZP →+* ↥F)
    -- decoder facts
    (hhalf : HalfEqF d.a9 d.hinv → (wideDecode B w (raw.sem 24) - 1 / 2) * y = 1)
    (hup : ∀ (i : Fin 25) (k : Fin 4), raw.sem i (Fin.natAdd 4 k) = 0)
    (hnq : raw.queries.length = d.nq)
    (hz : ∀ j, (raw.circle j).1.1 ∈ K4 B hB ∧ (raw.circle j).1.2 ∈ K4 B hB)
    (hrw : d.rw = 1084)
    -- QPrime builder identifications
    (src : Fin d.N → M K F) (stO : ℕ → ℕ)
    (hOwn : ∀ (i : Fin (wO raw.queries.length)) (t : Fin d.N),
      flatO B hB raw.queries (R0Z.SilentReduction.ownMap (Bat := R1Bat) π B (decode B w raw) (src t)) i =
        φ (blockM d.own d.os d.lane d.wl stO i t))
    (hRound : ∀ (i : Fin 1084) (t : Fin d.N),
      flat B hB (z4c (R0Z.Z4Maps.roundMaskMap (Bat := R1Bat) π B (decode B w raw) (src t))) i =
        φ (colM d.round d.rw i t))
    (hChain : ∀ i t : Fin 1084, chainTarget B hB (alpha (decode B w raw)) i t = φ (rowM d.tq d.rw i t))
    -- BCondG builder identifications
    (wb : Module.Basis (Fin 8) F K) {nf : ℕ} (fp : Fin nf → Fin 262144)
    (hcov : ∀ p, FoldedOpen (decode B w raw) p → ∃ f, fp f = p)
    (hbw : d.bw = (78 + nf) * 8)
    (sel : Fin d.NG → Fin 1024 × Fin 4) (stG : ℕ → ℕ)
    (hGOwn : ∀ (i : Fin (wO raw.queries.length)) (t : Fin d.NG),
      flatO B hB raw.queries (R0Z.SilentReduction.ownMap (Bat := R1Bat) π B (decode B w raw)
        (gSrc (sel t).1 (sel t).2)) i = φ (blockM d.gown d.gw d.glane d.gwl stG i t))
    (hGRound : ∀ (i : Fin 1084) (t : Fin d.NG),
      flat B hB (z4c (R0Z.Z4Maps.roundMaskMap (Bat := R1Bat) π B (decode B w raw)
        (gSrc (sel t).1 (sel t).2))) i = φ (colM d.ground d.rw i t))
    (hGBat : ∀ (i : Fin ((78 + nf) * 8)) (t : Fin d.NG),
      flatB wb fp (R0Z.SilentReduction.batMap (Bat := R1Bat) π B (decode B w raw)
        (gSrc (sel t).1 (sel t).2)) i = φ (colM d.gbat d.bw i t))
    -- lift builder identifications
    (hnl : 17 ≤ d.nl)
    (sel1 : Fin 16 → Fin (24 + 4 * raw.queries.length) → Fin 1024)
    (hsel1 : ∀ c t, eligible (Fin.castLE (by omega) c) (sel1 c t) ∧ sel1 c t ≠ 1023)
    (hlw1 : ∀ c : Fin 16, d.lw c = 24 + 4 * raw.queries.length)
    (hC1 : ∀ (c : Fin 16) (i x : Fin (24 + 4 * raw.queries.length)),
      R1Z.RfObs.colC1 (Bat := R1Bat) B hB π (decode B w raw) (Fin.castLE (by omega) c) raw.queries
        (sel1 c) i x = φ (d.lo (d.loff c + i * (24 + 4 * raw.queries.length) + x)))
    (selH : Fin (24 + 16 * raw.queries.length) → Fin 1024 × Fin 4)
    (hselH : ∀ t, (selH t).1 ≠ 0 ∧ (selH t).1 ∈ copyInactiveRows)
    (hlwH : d.lw 16 = 24 + 16 * raw.queries.length)
    (hH1 : ∀ i x : Fin (24 + 16 * raw.queries.length),
      R1Z.RfObs.colH1 (Bat := R1Bat) B hB π (decode B w raw) raw.queries selH i x =
        φ (d.lo (d.loff 16 + i * (24 + 16 * raw.queries.length) + x)))
    -- relation builder model (replaces rows and hRel)
    (hwb : ∀ k : Fin 8, wb k = wbP B.i B.u w k.val)
    (hinj : Function.Injective fp) (Fp : ℕ → ℕ) (hFp : ∀ f : Fin nf, Fp f.val = (fp f).val)
    (A Z : ℕ → K) (T TI : ℕ → ℕ) (Fl : ℕ → K) (κ α0 α1 Q H : K)
    (hA : ∀ (j : ℕ) (h : j < 10), A j = alpha (decode B w raw) ⟨j, h⟩)
    (hZx : ∀ j : Fin 2, Z (2 * j.val) = ((decode B w raw).circle j).1.1)
    (hZy : ∀ j : Fin 2, Z (2 * j.val + 1) = ((decode B w raw).circle j).1.2)
    (hT : ∀ r : Fin 1024, T r.val = (π r).val)
    (hFl : ∀ r : Fin 1024, Fl r.val = if r ∈ copyInactiveRows then 1 else 0)
    (hTI : ∀ j : Fin 1024, TI j.val = (π.symm j).val)
    (hκ : κ = (decode B w raw).opening 1) (hα0 : α0 = (decode B w raw).opening 2)
    (hα1 : α1 = (decode B w raw).opening 3) (hQ : Q = AspisR1.RoundPairing.quarter) (hH : H = 1 / 2)
    (rk ru : ℕ → ℕ) (L0 L1 L2 X : ℕ → K)
    (hU1 : ∀ ρ, ru ρ < 262144)
    (hU2 : ∀ ρ, 8 * ρ < d.q → 3 ≤ rk ρ →
      (⟨ru ρ % 262144, Nat.mod_lt _ (by norm_num)⟩ : Fin 262144) ∈ (decode B w raw).queries)
    (hL0 : ∀ ρ, 8 * ρ < d.q → 4 ≤ rk ρ → L0 ρ = algebraMap (ZMod AspisCircleGroupOrder.P) K
      (R1Z.BatchedAlgebra.lineInverse ⟨ru ρ / 4, by have := hU1 ρ; omega⟩ 0))
    (hL1 : ∀ ρ, 8 * ρ < d.q → 4 ≤ rk ρ → L1 ρ = algebraMap (ZMod AspisCircleGroupOrder.P) K
      (R1Z.BatchedAlgebra.lineInverse ⟨ru ρ / 4, by have := hU1 ρ; omega⟩ 1))
    (hL2 : ∀ ρ, 8 * ρ < d.q → 4 ≤ rk ρ → L2 ρ = algebraMap (ZMod AspisCircleGroupOrder.P) K
      (R1Z.BatchedAlgebra.lineInverse ⟨ru ρ / 4, by have := hU1 ρ; omega⟩ 2))
    (hX : ∀ ρ, 8 * ρ < d.q → 4 ≤ rk ρ → X ρ = algebraMap (ZMod AspisCircleGroupOrder.P) K
      (AspisV5FriReleasedLineGeometry.storedLine16X ⟨ru ρ / 4, by have := hU1 ρ; omega⟩))
    (hent : RelEntry ((Subfield.subtype F).comp φ) B.i B.u w d.rel d.bw d.q (fun ρ c =>
      coefP nf α0 α1 Q (w2P A Z T TI Fl κ α0 α1 Q) Fp (lfvP H α1 (L0 ρ) (L1 ρ) (L2 ρ))
        (fun e => natP (X ρ) e 10) (rk ρ) (ru ρ) c)) :
    P_R1 π B hB (decode B w raw) :=
  p_r1_of_data π B hB w raw y d hd φ hhalf hup hnq hz hrw src stO hOwn hRound hChain wb fp hcov hbw
    (relRows rk ru) sel stG
    (rel_data π (decode B w raw) φ B.i B.u w wb hwb fp hinj Fp hFp A Z T TI Fl κ α0 α1 Q H hA hZx hZy hT hFl
      hTI hκ hα0 hα1 hQ hH rk ru L0 L1 L2 X hbw hU1 hU2 hL0 hL1 hL2 hX d.rel hent)
    hGOwn hGRound hGBat hnl sel1 hsel1 hlw1 hC1 selH hselH hlwH hH1

#print axioms p_r1_of_data_rel

end R1Z.CertCheckSound

end
