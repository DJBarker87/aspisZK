import R1Z.CertCheckData
import R1Z.CertCheckSound

/-! D49.4 C3 / D38.5: **`check_sound`** — the extracted Rust checker returning
`true` implies `P_R1` on the decoded record, given the builder identifications
and decoder facts of `CertCheckSound.p_r1_of_data` on `toData pb ct`.
`check_data` ∘ `p_r1_of_data`. -/

set_option autoImplicit false

noncomputable section

namespace R1Z.CertCheckSound

open scoped BigOperators
open Aeneas Aeneas.Std Result R1CertCheck R1Z.CertCheck
open R0P R0Z.MaskLayout R0Z.HonestView R0Z.Partition R0Z.K4
open R1Z.Batched R1Z.VerifierRelationsR1 R1Z.PredicateR1 R1Z.CertSound R1Z.CertR1
open R1Z.RfDec R1Z.RfSrc R1Z.RfChain R1Z.RfOwnLimb R1Z.RfBat R1Z.CertData

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K] {F : Subfield K}

variable (pb : Pub) (ct : Cert)

/-- **`check_sound`**: the extracted checker accepts ⟹ `P_R1` (decode). -/
theorem check_sound (hc : check pb ct = ok true) (π : Fin 1024 ≃ Fin 1024) (B : PackBasis F) (hB : PackField B)
    (w : K) (raw : RawChallenges K F) (y : K) (φ : R1Z.CertData.ZP →+* ↥F)
    -- decoder facts
    (hhalf : HalfEqF (toData pb ct).a9 (toData pb ct).hinv → (wideDecode B w (raw.sem 24) - 1 / 2) * y = 1)
    (hup : ∀ (i : Fin 25) (k : Fin 4), raw.sem i (Fin.natAdd 4 k) = 0)
    (hnq : raw.queries.length = (toData pb ct).nq)
    (hz : ∀ j, (raw.circle j).1.1 ∈ K4 B hB ∧ (raw.circle j).1.2 ∈ K4 B hB)
    (hrw : (toData pb ct).rw = 1084)
    -- QPrime builder identifications
    (src : Fin (toData pb ct).N → M K F) (stO : ℕ → ℕ)
    (hOwn : ∀ (i : Fin (wO raw.queries.length)) (t : Fin (toData pb ct).N),
      flatO B hB raw.queries (R0Z.SilentReduction.ownMap (Bat := R1Bat) π B (decode B w raw) (src t)) i =
        φ (blockM (toData pb ct).own (toData pb ct).os (toData pb ct).lane (toData pb ct).wl stO i t))
    (hRound : ∀ (i : Fin 1084) (t : Fin (toData pb ct).N),
      flat B hB (z4c (R0Z.Z4Maps.roundMaskMap (Bat := R1Bat) π B (decode B w raw) (src t))) i =
        φ (colM (toData pb ct).round (toData pb ct).rw i t))
    (hChain : ∀ i t : Fin 1084, chainTarget B hB (alpha (decode B w raw)) i t = φ (rowM (toData pb ct).tq (toData pb ct).rw i t))
    -- BCondG builder identifications
    (wb : Module.Basis (Fin 8) F K) {nf : ℕ} (fp : Fin nf → Fin 262144)
    (hcov : ∀ p, FoldedOpen (decode B w raw) p → ∃ f, fp f = p)
    (hbw : (toData pb ct).bw = (78 + nf) * 8)
    (rows : Fin (toData pb ct).q → R1Rel × Fin 8) (sel : Fin (toData pb ct).NG → Fin 1024 × Fin 4) (stG : ℕ → ℕ)
    (hRel : ∀ (x : Fin (toData pb ct).q) (c : Fin ((78 + nf) * 8)),
      relMat wb π (decode B w raw) fp rows x c = φ (rowM (toData pb ct).rel (toData pb ct).bw x c))
    (hGOwn : ∀ (i : Fin (wO raw.queries.length)) (t : Fin (toData pb ct).NG),
      flatO B hB raw.queries (R0Z.SilentReduction.ownMap (Bat := R1Bat) π B (decode B w raw)
        (gSrc (sel t).1 (sel t).2)) i = φ (blockM (toData pb ct).gown (toData pb ct).gw (toData pb ct).glane (toData pb ct).gwl stG i t))
    (hGRound : ∀ (i : Fin 1084) (t : Fin (toData pb ct).NG),
      flat B hB (z4c (R0Z.Z4Maps.roundMaskMap (Bat := R1Bat) π B (decode B w raw)
        (gSrc (sel t).1 (sel t).2))) i = φ (colM (toData pb ct).ground (toData pb ct).rw i t))
    (hGBat : ∀ (i : Fin ((78 + nf) * 8)) (t : Fin (toData pb ct).NG),
      flatB wb fp (R0Z.SilentReduction.batMap (Bat := R1Bat) π B (decode B w raw)
        (gSrc (sel t).1 (sel t).2)) i = φ (colM (toData pb ct).gbat (toData pb ct).bw i t))
    -- lift builder identifications
    (hnl : 17 ≤ (toData pb ct).nl)
    (sel1 : Fin 16 → Fin (24 + 4 * raw.queries.length) → Fin 1024)
    (hsel1 : ∀ c t, eligible (Fin.castLE (by omega) c) (sel1 c t) ∧ sel1 c t ≠ 1023)
    (hlw1 : ∀ c : Fin 16, (toData pb ct).lw c = 24 + 4 * raw.queries.length)
    (hC1 : ∀ (c : Fin 16) (i x : Fin (24 + 4 * raw.queries.length)),
      R1Z.RfObs.colC1 (Bat := R1Bat) B hB π (decode B w raw) (Fin.castLE (by omega) c) raw.queries
        (sel1 c) i x = φ ((toData pb ct).lo ((toData pb ct).loff c + i * (24 + 4 * raw.queries.length) + x)))
    (selH : Fin (24 + 16 * raw.queries.length) → Fin 1024 × Fin 4)
    (hselH : ∀ t, (selH t).1 ≠ 0 ∧ (selH t).1 ∈ copyInactiveRows)
    (hlwH : (toData pb ct).lw 16 = 24 + 16 * raw.queries.length)
    (hH1 : ∀ i x : Fin (24 + 16 * raw.queries.length),
      R1Z.RfObs.colH1 (Bat := R1Bat) B hB π (decode B w raw) raw.queries selH i x =
        φ ((toData pb ct).lo ((toData pb ct).loff 16 + i * (24 + 16 * raw.queries.length) + x))) :
    P_R1 π B hB (decode B w raw) :=
  p_r1_of_data π B hB w raw y (toData pb ct) (check_data hc) φ hhalf hup hnq hz hrw src stO hOwn hRound
    hChain wb fp hcov hbw rows sel stG hRel hGOwn hGRound hGBat hnl sel1 hsel1 hlw1 hC1 selH hselH hlwH hH1

#print axioms check_sound

end R1Z.CertCheckSound

end
