import R1Z.CertR1Full
import R1Z.CertData2

/-! D49.4 C3: `check_sound` on the checker's flat data.

`p_r1_of_data`: if the checker's tests hold on the flat data `d` (`DataOK d`,
which the extracted `check pb c = ok true` gives for `d = toData pb c`,
`CertCheckData.check_data`), then `P_R1` holds on the decoded record, given

* the **builder identifications** (C3 / D53.2, kept as named hypotheses): every
  column matrix the checker reads is `φ` of the Lean coordinates — own
  (`hOwn`, `hGOwn`, through the lane-block layouts `stO`, `stG`), round
  (`hRound`, `hGRound`), batched (`hGBat`), the relR1 limb functionals (`hRel`),
  the ChainT0K4 targets (`hChain`) and the lift observation columns (`hC1`, `hH1`)
  with the lift widths (`hlw1`, `hlwH`);
* the decoder facts: the QM31 limb equations of HalfOK give the `K` equation
  (`hhalf`), the upper limbs vanish (`hup`), the query count (`hnq`), the
  circle points in `K₄` (`hz`), the dimensions (`hrw`, `hbw`, `hnl`);
* `p_r1_of_checks`'s remaining facts: `wb`, `hcov`, `hsel1`, `hselH`.

`φ : ZMod (2^31-1) →+* F` is any ring hom (the prime-field embedding). -/

set_option autoImplicit false

noncomputable section

namespace R1Z.CertCheckSound

open scoped BigOperators
open R0P R0Z.MaskLayout R0Z.HonestView R0Z.Partition R0Z.K4
open R1Z.Batched R1Z.VerifierRelationsR1 R1Z.PredicateR1 R1Z.CertSound R1Z.CertR1
open R1Z.RfDec R1Z.RfSrc R1Z.RfChain R1Z.RfOwnLimb R1Z.RfBat R1Z.CertData

section Congr

variable {G : Type*} [Field G]

theorem preOK_of_eq {a b N m n : ℕ} {Zc Zc' : Fin a → Fin N → G} {Gc Gc' : Fin b → Fin N → G}
    {ents : Fin m → KerEntry N G} {Y : Fin n → Fin m → G} {T T' : Fin n → Fin b → G}
    (hZ : ∀ i t, Zc i t = Zc' i t) (hG : ∀ i t, Gc i t = Gc' i t) (hT : ∀ i t, T i t = T' i t)
    (h : PreOK Zc' Gc' ents Y T') : PreOK Zc Gc ents Y T := by
  have e1 : Zc = Zc' := funext fun i => funext fun t => hZ i t
  have e2 : Gc = Gc' := funext fun i => funext fun t => hG i t
  have e3 : T = T' := funext fun i => funext fun t => hT i t
  subst e1 e2 e3
  exact h

theorem preOK₂_of_eq {a₁ a₂ b N m n : ℕ} {Z₁ Z₁' : Fin a₁ → Fin N → G} {Z₂ Z₂' : Fin a₂ → Fin N → G}
    {Gc Gc' : Fin b → Fin N → G} {ents : Fin m → KerEntry N G} {Y : Fin n → Fin m → G}
    {T : Fin n → Fin b → G}
    (h1 : ∀ i t, Z₁ i t = Z₁' i t) (h2 : ∀ i t, Z₂ i t = Z₂' i t) (hG : ∀ i t, Gc i t = Gc' i t)
    (h : PreOK₂ Z₁' Z₂' Gc' ents Y T) : PreOK₂ Z₁ Z₂ Gc ents Y T := by
  have e1 : Z₁ = Z₁' := funext fun i => funext fun t => h1 i t
  have e2 : Z₂ = Z₂' := funext fun i => funext fun t => h2 i t
  have e3 : Gc = Gc' := funext fun i => funext fun t => hG i t
  subst e1 e2 e3
  exact h

theorem rinvOK_of_eq {w : ℕ} {O O' U : Fin w → Fin w → G} (hO : ∀ i x, O i x = O' i x)
    (h : RinvOK O' U) : RinvOK O U := by
  have e : O = O' := funext fun i => funext fun x => hO i x
  subst e
  exact h

end Congr

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K] {F : Subfield K}

/-- **`P_R1` from the checker's flat data** (with the builder identifications
and decoder facts as named hypotheses). -/
theorem p_r1_of_data (π : Fin 1024 ≃ Fin 1024) (B : PackBasis F) (hB : PackField B)
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
    (rows : Fin d.q → R1Rel × Fin 8) (sel : Fin d.NG → Fin 1024 × Fin 4) (stG : ℕ → ℕ)
    (hRel : ∀ (x : Fin d.q) (c : Fin ((78 + nf) * 8)),
      relMat wb π (decode B w raw) fp rows x c = φ (rowM d.rel d.bw x c))
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
        φ (d.lo (d.loff 16 + i * (24 + 16 * raw.queries.length) + x))) :
    P_R1 π B hB (decode B w raw) := by
  obtain ⟨entsQ, hQ⟩ := data_qprime φ d hd stO (A := wO raw.queries.length) hrw
  obtain ⟨entsG, hG⟩ := data_vg φ d hd stG (A := wO raw.queries.length) hrw hbw
  have hE := data_ech φ d hd hbw
  have hrelF : relMat wb π (decode B w raw) fp rows =
      fun (x : Fin d.q) (c : Fin ((78 + nf) * 8)) => φ (rowM d.rel d.bw x c) :=
    funext fun x => funext fun c => hRel x c
  have hl : raw.queries.length ≤ 22 := by rw [hnq]; exact hd.2.1
  refine R1Z.CertR1Full.p_r1_of_checks π B hB w raw y (hhalf hd.1) hup hl hz src entsQ
    (fun i e => φ (rowM d.y d.m i e))
    (preOK_of_eq hOwn hRound hChain hQ) wb fp hcov rows sel (fun a x => φ (rowM d.u d.q a x))
    (pivF d hd hbw) (frF d hd hbw) (by rw [hrelF]; exact hE) entsG (fun f e => φ (rowM d.yg d.mg f e))
    (by rw [hrelF]; exact preOK₂_of_eq hGOwn hGRound hGBat hG) sel1 hsel1
    (fun c x j => φ (d.lu (d.loff c + x * (24 + 4 * raw.queries.length) + j)))
    (fun c => rinvOK_of_eq (hC1 c) (data_lift φ d hd c (by omega) (hlw1 c))) selH hselH
    (fun x j => φ (d.lu (d.loff 16 + x * (24 + 16 * raw.queries.length) + j)))
    (rinvOK_of_eq hH1 (data_lift φ d hd 16 (by omega) hlwH))

#print axioms preOK_of_eq
#print axioms preOK₂_of_eq
#print axioms rinvOK_of_eq
#print axioms p_r1_of_data

end R1Z.CertCheckSound

end
