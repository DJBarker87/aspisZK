import R1Z.CertCheckSoundAll
import R1Z.CertBuildIdent2

/-! D57.3: **`check_sound'`** — `check_sound` with the chain-target
identification `hChain` and the HalfOK decoder fact `hhalf` discharged: the
prover builds `pb.tq` with the extracted `fill_tq` (`hbuild`), and the remaining
facts are the QM31 tower premise `hT` (`i² = -1`, `u² = 2 + i` for the packing
basis) and the limb correspondence of the alpha challenges (`hal`, `ha9`). -/

set_option autoImplicit false

noncomputable section

namespace R1Z.CertCheckSound

open scoped BigOperators
open Aeneas Aeneas.Std Result R1CertCheck R1Z.CertCheck R1Z.CertBuild
open R0P R0Z.MaskLayout R0Z.HonestView R0Z.Partition R0Z.K4
open R1Z.Batched R1Z.VerifierRelationsR1 R1Z.PredicateR1 R1Z.CertSound R1Z.CertR1
open R1Z.RfDec R1Z.RfSrc R1Z.RfChain R1Z.RfOwnLimb R1Z.RfBat R1Z.CertData

attribute [local instance] Classical.propDecidable

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K] {F : Subfield K}

theorem wide_lo (B : PackBasis F) (w : K) (l : Fin 8 → F) (h : ∀ k : Fin 4, l (Fin.natAdd 4 k) = 0) :
    wideDecode B w l = pack4 B (fun k => (l (Fin.castAdd 4 k) : K)) := by
  have e4 : l 4 = 0 := h 0
  have e5 : l 5 = 0 := h 1
  have e6 : l 6 = 0 := h 2
  have e7 : l 7 = 0 := h 3
  unfold wideDecode RfDec.lo RfDec.hi
  simp [e4, e5, e6, e7, pack4]

theorem alimb_eq (B : PackBasis F) (φ : R1Z.CertData.ZP →+* ↥F) (w : K) (raw : RawChallenges K F)
    (hup : ∀ (i : Fin 25) (k : Fin 4), raw.sem i (Fin.natAdd 4 k) = 0) (al : Slice U32)
    (hal : ∀ (j : Fin 10) (k : Fin 4), ((φ (gs al (4 * j.val + k.val)) : F) : K) =
      ((raw.sem ⟨15 + j.val, by omega⟩ (Fin.castAdd 4 k) : F) : K)) (j : Fin 10) :
    Alimb B φ al j.val = alpha (decode B w raw) j := by
  rw [decode_alpha, wide_lo B w _ (hup _)]
  unfold Alimb ψ4 pack4 embR
  have h0 : ((φ (gs al (4 * j.val)) : F) : K) = ((raw.sem ⟨15 + j.val, by omega⟩ (Fin.castAdd 4 0) : F) : K) := hal j 0
  have h1 : ((φ (gs al (4 * j.val + 1)) : F) : K) = ((raw.sem ⟨15 + j.val, by omega⟩ (Fin.castAdd 4 1) : F) : K) := hal j 1
  have h2 : ((φ (gs al (4 * j.val + 2)) : F) : K) = ((raw.sem ⟨15 + j.val, by omega⟩ (Fin.castAdd 4 2) : F) : K) := hal j 2
  have h3 : ((φ (gs al (4 * j.val + 3)) : F) : K) = ((raw.sem ⟨15 + j.val, by omega⟩ (Fin.castAdd 4 3) : F) : K) := hal j 3
  simp only [RingHom.coe_comp, Function.comp_apply, Subfield.coe_subtype]
  rw [h0, h1, h2, h3]

theorem half_from (B : PackBasis F) (φ : R1Z.CertData.ZP →+* ↥F) (hT : Tower B) (w : K) (raw : RawChallenges K F)
    (hup : ∀ (i : Fin 25) (k : Fin 4), raw.sem i (Fin.natAdd 4 k) = 0) (a9 hinv : Slice U32)
    (ha9 : ∀ k : Fin 4, ((φ (gs a9 k.val) : F) : K) = ((raw.sem 24 (Fin.castAdd 4 k) : F) : K))
    (hh : HalfEqF (gs a9) (gs hinv)) :
    Hlimb B φ hinv * (wideDecode B w (raw.sem 24) - 1 / 2) = 1 := by
  obtain ⟨e0, e1, e2, e3⟩ := hh
  have m := psi4_mul B φ hT (gs a9 0 - 1073741824) (gs a9 1) (gs a9 2) (gs a9 3)
    (gs hinv 0) (gs hinv 1) (gs hinv 2) (gs hinv 3)
  have q0 : qmulZ (gs a9 0 - 1073741824) (gs a9 1) (gs a9 2) (gs a9 3) (gs hinv 0) (gs hinv 1) (gs hinv 2) (gs hinv 3) 0 = 1 := e0
  have q1 : qmulZ (gs a9 0 - 1073741824) (gs a9 1) (gs a9 2) (gs a9 3) (gs hinv 0) (gs hinv 1) (gs hinv 2) (gs hinv 3) 1 = 0 := e1
  have q2 : qmulZ (gs a9 0 - 1073741824) (gs a9 1) (gs a9 2) (gs a9 3) (gs hinv 0) (gs hinv 1) (gs hinv 2) (gs hinv 3) 2 = 0 := e2
  have q3 : qmulZ (gs a9 0 - 1073741824) (gs a9 1) (gs a9 2) (gs a9 3) (gs hinv 0) (gs hinv 1) (gs hinv 2) (gs hinv 3) 3 = 0 := e3
  rw [q0, q1, q2, q3] at m
  have one : ψ4 B φ (1 : R1Z.CertCheck.ZP) 0 0 0 = (1 : K) := by simp [ψ4]
  have av : ψ4 B φ (gs a9 0 - 1073741824) (gs a9 1) (gs a9 2) (gs a9 3) =
      wideDecode B w (raw.sem 24) - 1 / 2 := by
    rw [wide_lo B w _ (hup 24), ← embR_half φ]
    have h0 : ((φ (gs a9 0) : F) : K) = ((raw.sem 24 (Fin.castAdd 4 0) : F) : K) := ha9 0
    have h1 : ((φ (gs a9 1) : F) : K) = ((raw.sem 24 (Fin.castAdd 4 1) : F) : K) := ha9 1
    have h2 : ((φ (gs a9 2) : F) : K) = ((raw.sem 24 (Fin.castAdd 4 2) : F) : K) := ha9 2
    have h3 : ((φ (gs a9 3) : F) : K) = ((raw.sem 24 (Fin.castAdd 4 3) : F) : K) := ha9 3
    unfold ψ4 pack4 embR
    simp only [map_sub, RingHom.coe_comp, Function.comp_apply, Subfield.coe_subtype, Subfield.coe_sub]
    rw [h0, h1, h2, h3]
    ring
  rw [one, av] at m
  rw [Hlimb, mul_comm, ← m]

variable (pb : Pub) (ct : Cert)

/-- **`check_sound'`**: `check_sound` with `hChain` and `hhalf` discharged by the
extracted chain-target builder. -/
theorem check_sound' (hc : check pb ct = ok true) (π : Fin 1024 ≃ Fin 1024) (B : PackBasis F) (hB : PackField B)
    (w : K) (raw : RawChallenges K F) (φ : R1Z.CertData.ZP →+* ↥F)
    -- decoder facts
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
    -- chain-target builder (replaces hChain and hhalf): the tower premise, the alpha limbs, the builder run
    (hT : Tower B) (al : Slice U32)
    (hal : ∀ (j : Fin 10) (k : Fin 4), ((φ (gs al (4 * j.val + k.val)) : F) : K) =
      ((raw.sem ⟨15 + j.val, by omega⟩ (Fin.castAdd 4 k) : F) : K))
    (ha9 : ∀ k : Fin 4, ((φ (gs (sl pb.a9) k.val) : F) : K) = ((raw.sem 24 (Fin.castAdd 4 k) : F) : K))
    (hbuild : R1CertBuild.fill_tq al (sl ct.hinv) = ok pb.tq)
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
    P_R1 π B hB (decode B w raw) := by
  have hd := check_data hc
  have hA : ∀ j : Fin 10, Alimb B φ al j.val = alpha (decode B w raw) j := alimb_eq B φ w raw hup al hal
  have hH := half_from B φ hT w raw hup (sl pb.a9) (sl ct.hinv) ha9 hd.1
  have hCh := chain_ident B φ hT hB al (sl ct.hinv) (alpha (decode B w raw)) hA (by
    rw [decode_alpha_nine]; exact hH) hbuild
  refine check_sound pb ct hc π B hB w raw (Hlimb B φ (sl ct.hinv)) φ
    (fun _ => by rw [mul_comm]; exact hH) hup hnq hz hrw src stO hOwn hRound
    (fun i t => by
      rw [hCh i t]
      show φ (gs (alloc.vec.Vec.deref pb.tq) (i.val * 1084 + t.val)) =
        φ (gs (sl pb.tq) (i.val * pb.rw.val + t.val))
      rw [show pb.rw.val = 1084 from hrw])
    wb fp hcov hbw rows sel stG hRel hGOwn hGRound hGBat hnl sel1 hsel1 hlw1 hC1 selH hselH hlwH hH1

#print axioms alimb_eq
#print axioms half_from
#print axioms check_sound'

end R1Z.CertCheckSound

end
