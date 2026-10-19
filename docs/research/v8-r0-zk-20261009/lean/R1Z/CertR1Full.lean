import R1Z.CertR1Lift
import R1Z.RfOwnLimb
import R1Z.RfRound
import R1Z.RfBat

/-! D49.4 C2: `P_R1` from the checker's tests alone (every rf_* premise discharged).

With the coordinate embeddings fixed —
`ιo = RfOwnLimb.iotaO l`, `ιr = RfChain.iotaR`, `ιb = RfBat.iotaB wb fp`,
`ι = RfObs.iotaC1 l` / `iotaH1 l` — and the column matrices the Lean maps'
coordinates of each source (`flatO ∘ ownMap`, `flat ∘ z4c ∘ roundMaskMap`,
`flatB ∘ batMap`, `RfBat.relMat`, `RfObs.colC1/colH1`, `RfChain.chainTarget`),
the `P_R1` conjuncts follow from the Props the checker decides (`PreOK`,
`PreOK₂`, `EchOK`, `RinvOK`, the half inverse, the limb and length checks)
plus these named facts, none of which is a row-formula premise:

* decoder/instance facts: the record is `RfDec.decode B w raw`; the circle
  points are in `K₄` (`hz`, the Rust `z` are QM31 points); `wb` is an `F`-basis
  of `K` (the WideExact limbs); the opened folded list `fp` covers the open
  folded cells (`hcov`);
* one-index side conditions of the selected lift sources (`hsel1`, `hselH`).

What remains for `check_sound` is C3: that the extracted Rust checker builds
exactly these matrices (whose closed forms are `RfOwn.ownMap_*Src`,
`RfObs.obs_balWord_*`, `RfLine`), and decides exactly these Props. -/

set_option autoImplicit false

noncomputable section

namespace R1Z.CertR1Full

open scoped BigOperators
open R0P R0Z.MaskLayout R0Z.HonestView R0Z.Partition R0Z.K4
open R1Z.Batched R1Z.VerifierRelationsR1 R1Z.PredicateR1 R1Z.CertSound R1Z.CertR1
open R1Z.RfDec R1Z.RfSrc R1Z.RfChain R1Z.RfOwnLimb R1Z.RfBat

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K] {F : Subfield K}

/-- QPrime_R1 from the two-level preimage check alone. -/
theorem qprime_of_checks (π : Fin 1024 ≃ Fin 1024) (B : PackBasis F) (hB : PackField B)
    (ch : Challenges K) (hsem : SemK4 B hB ch) (l : List (Fin 262144))
    (hq : ch.queries = l.toFinset)
    (hz : ∀ j, (ch.circle j).1.1 ∈ K4 B hB ∧ (ch.circle j).1.2 ∈ K4 B hB)
    {N m : ℕ} (src : Fin N → M K F) (ents : Fin m → KerEntry N F) (Y : Fin 1084 → Fin m → F)
    (h : PreOK (fun i t => flatO B hB l (R0Z.SilentReduction.ownMap (Bat := R1Bat) π B ch (src t)) i)
      (fun i t => flat B hB (z4c (R0Z.Z4Maps.roundMaskMap (Bat := R1Bat) π B ch (src t))) i)
      ents Y (chainTarget B hB (alpha ch))) :
    QPrime_R1 π B hB ch :=
  qprime_of_cert π B hB ch src _ _ (iotaO B l) (iotaR B (alpha ch))
    (rf_own_col B hB π ch l hq (fun j => hsem _) hz src)
    (R1Z.RfRound.rf_round B hB π ch hsem src) (chainTarget B hB (alpha ch))
    (rf_chain (Bat := R1Bat) B hB ch (fun j => hsem _)) ents Y h

/-- BCondG_R1 from the echelon check and the G-preimage check alone. -/
theorem bcondG_of_checks (π : Fin 1024 ≃ Fin 1024) (B : PackBasis F) (hB : PackField B)
    (ch : Challenges K) (hsem : SemK4 B hB ch) (l : List (Fin 262144))
    (hq : ch.queries = l.toFinset)
    (hz : ∀ j, (ch.circle j).1.1 ∈ K4 B hB ∧ (ch.circle j).1.2 ∈ K4 B hB)
    (wb : Module.Basis (Fin 8) F K) {nf : ℕ} (fp : Fin nf → Fin 262144)
    (hcov : ∀ p, FoldedOpen ch p → ∃ f, fp f = p) {q : ℕ} (rows : Fin q → R1Rel × Fin 8)
    {NG mG r k : ℕ} (sel : Fin NG → Fin 1024 × Fin 4)
    (U : Fin r → Fin q → F) (piv : Fin r → Fin ((78 + nf) * 8)) (fr : Fin k → Fin ((78 + nf) * 8))
    (hE : EchOK (Emat U (relMat wb π ch fp rows)) piv fr)
    (ents : Fin mG → KerEntry NG F) (YG : Fin k → Fin mG → F)
    (h : PreOK₂
      (fun i t => flatO B hB l (R0Z.SilentReduction.ownMap (Bat := R1Bat) π B ch
        (gSrc (sel t).1 (sel t).2)) i)
      (fun i t => flat B hB (z4c (R0Z.Z4Maps.roundMaskMap (Bat := R1Bat) π B ch
        (gSrc (sel t).1 (sel t).2))) i)
      (fun i t => flatB wb fp (R0Z.SilentReduction.batMap (Bat := R1Bat) π B ch
        (gSrc (sel t).1 (sel t).2)) i)
      ents YG (fun f => nvec (Emat U (relMat wb π ch fp rows)) piv fr f)) :
    BCondG_R1 π B ch :=
  bcondG_of_cert π B ch (fun t => gSrc (sel t).1 (sel t).2)
    (fun t => gSrc_mem_Gonly (sel t).1 (sel t).2) _ _ _ (iotaO B l) (iotaR B (alpha ch))
    (iotaB wb fp) (rf_own_col B hB π ch l hq (fun j => hsem _) hz _)
    (R1Z.RfRound.rf_round B hB π ch hsem _)
    (fun t => rf_bat wb π B ch fp hcov _) (relMat wb π ch fp rows)
    (rf_rel wb π ch fp hcov rows) U piv fr hE ents YG h

/-- **`P_R1` from the checker's tests.**  On the decoded record, every conjunct
follows from the Props the checker decides, the decoder/instance facts
(`hz`, `wb`, `hcov`) and the selected-index side conditions. -/
theorem p_r1_of_checks (π : Fin 1024 ≃ Fin 1024) (B : PackBasis F) (hB : PackField B)
    (w : K) (raw : RawChallenges K F) (y : K)
    (hy : (wideDecode B w (raw.sem 24) - 1 / 2) * y = 1)
    (hup : ∀ (i : Fin 25) (k : Fin 4), raw.sem i (Fin.natAdd 4 k) = 0)
    (hl : raw.queries.length ≤ 22)
    (hz : ∀ j, (raw.circle j).1.1 ∈ K4 B hB ∧ (raw.circle j).1.2 ∈ K4 B hB)
    -- QPrime
    {N m : ℕ} (src : Fin N → M K F) (ents : Fin m → KerEntry N F) (Y : Fin 1084 → Fin m → F)
    (hQ : PreOK (fun i t => flatO B hB raw.queries
        (R0Z.SilentReduction.ownMap (Bat := R1Bat) π B (decode B w raw) (src t)) i)
      (fun i t => flat B hB (z4c (R0Z.Z4Maps.roundMaskMap (Bat := R1Bat) π B (decode B w raw)
        (src t))) i)
      ents Y (chainTarget B hB (alpha (decode B w raw))))
    -- BCondG
    (wb : Module.Basis (Fin 8) F K) {nf : ℕ} (fp : Fin nf → Fin 262144)
    (hcov : ∀ p, FoldedOpen (decode B w raw) p → ∃ f, fp f = p) {q : ℕ}
    (rows : Fin q → R1Rel × Fin 8) {NG mG r k : ℕ} (sel : Fin NG → Fin 1024 × Fin 4)
    (U : Fin r → Fin q → F) (piv : Fin r → Fin ((78 + nf) * 8)) (fr : Fin k → Fin ((78 + nf) * 8))
    (hE : EchOK (Emat U (relMat wb π (decode B w raw) fp rows)) piv fr)
    (entsG : Fin mG → KerEntry NG F) (YG : Fin k → Fin mG → F)
    (hG : PreOK₂
      (fun i t => flatO B hB raw.queries (R0Z.SilentReduction.ownMap (Bat := R1Bat) π B
        (decode B w raw) (gSrc (sel t).1 (sel t).2)) i)
      (fun i t => flat B hB (z4c (R0Z.Z4Maps.roundMaskMap (Bat := R1Bat) π B (decode B w raw)
        (gSrc (sel t).1 (sel t).2))) i)
      (fun i t => flatB wb fp (R0Z.SilentReduction.batMap (Bat := R1Bat) π B (decode B w raw)
        (gSrc (sel t).1 (sel t).2)) i)
      entsG YG (fun f => nvec (Emat U (relMat wb π (decode B w raw) fp rows)) piv fr f))
    -- lifts
    (sel1 : Fin 16 → Fin (24 + 4 * raw.queries.length) → Fin 1024)
    (hsel1 : ∀ c t, eligible (Fin.castLE (by omega) c) (sel1 c t) ∧ sel1 c t ≠ 1023)
    (U1 : Fin 16 → Fin (24 + 4 * raw.queries.length) → Fin (24 + 4 * raw.queries.length) → F)
    (h1 : ∀ c, RinvOK (R1Z.RfObs.colC1 (Bat := R1Bat) B hB π (decode B w raw)
      (Fin.castLE (by omega) c) raw.queries (sel1 c)) (U1 c))
    (selH : Fin (24 + 16 * raw.queries.length) → Fin 1024 × Fin 4)
    (hselH : ∀ t, (selH t).1 ≠ 0 ∧ (selH t).1 ∈ copyInactiveRows)
    (UH : Fin (24 + 16 * raw.queries.length) → Fin (24 + 16 * raw.queries.length) → F)
    (hH : RinvOK (R1Z.RfObs.colH1 (Bat := R1Bat) B hB π (decode B w raw) raw.queries selH) UH) :
    P_R1 π B hB (decode B w raw) :=
  R1Z.CertR1Lift.p_r1_of_decode_lifts π B hB w raw y hy hup hl hz
    (fun hsem => qprime_of_checks π B hB _ hsem raw.queries (decode_queries B w raw) hz src ents Y hQ)
    (bcondG_of_checks π B hB _ (R1Z.CertR1Rf.semK4_of_decode B hB w raw hup) raw.queries
      (decode_queries B w raw) hz wb fp hcov rows sel U piv fr hE entsG YG hG)
    sel1 hsel1 U1 h1 selH hselH UH hH

#print axioms qprime_of_checks
#print axioms bcondG_of_checks
#print axioms p_r1_of_checks

end R1Z.CertR1Full

end
