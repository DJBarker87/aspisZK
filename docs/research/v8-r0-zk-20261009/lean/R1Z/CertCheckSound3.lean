import R1Z.CertCheckSound2
import R1Z.CertLiftIdent4

/-! D59.2: **`check_sound''`** — `check_sound'` with the lift identifications
`hC1` and `hH1` discharged by the extracted lift-column builder `fill_lo`
(`hblo`).  New inputs under named premises (D59.2 ruling): the transport table
(`htr`), the OOD points (`hzx`, `hzy`), the stored points (`hsx`, `hsy`), the
copy-inactive flags (`hin`); plus the selection and offset layout of the lift
blocks (`hselC`, `hselHv`, `hloC`, `hloH`).  `natural` = `naturalLineValue` is
proved (`CertNatural.natR_eq`). -/

set_option autoImplicit false

noncomputable section

namespace R1Z.CertCheckSound

open scoped BigOperators
open Aeneas Aeneas.Std Result R1CertCheck R1Z.CertCheck R1Z.CertBuild
open R0P R0Z.MaskLayout R0Z.HonestView R0Z.Partition R0Z.K4
open R1Z.Batched R1Z.VerifierRelationsR1 R1Z.PredicateR1 R1Z.CertSound R1Z.CertR1
open R1Z.RfDec R1Z.RfSrc R1Z.RfChain R1Z.RfOwnLimb R1Z.RfBat R1Z.CertData R1Z.RfOwn R1Z.RfObs

attribute [local instance] Classical.propDecidable

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K] {F : Subfield K}

variable (pb : Pub) (ct : Cert)

/-- **`check_sound''`**. -/
theorem check_sound'' (hc : check pb ct = ok true) (π : Fin 1024 ≃ Fin 1024) (B : PackBasis F) (hB : PackField B)
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
    (selH : Fin (24 + 16 * raw.queries.length) → Fin 1024 × Fin 4)
    (hselH : ∀ t, (selH t).1 ≠ 0 ∧ (selH t).1 ∈ copyInactiveRows)
    (hlwH : (toData pb ct).lw 16 = 24 + 16 * raw.queries.length)
    -- lift-column builder (replaces hC1 and hH1): inputs under named premises (D59.2 ruling)
    (zz tr sx sy inact sel1a selha : Slice U32) (nqU : Usize) (hnqU : nqU.val = raw.queries.length)
    (hzx : ∀ j : Fin 2, Alimb B φ zz (2 * j.val) = (raw.circle j).1.1)
    (hzy : ∀ j : Fin 2, Alimb B φ zz (2 * j.val + 1) = (raw.circle j).1.2)
    (htr : ∀ r : Fin 1024, gN tr r.val = (π r).val)
    (hin : ∀ r : Fin 1024, gs inact r.val = if r ∈ copyInactiveRows then 1 else 0)
    (hsx : ∀ (m : ℕ) (hm : m < 4 * raw.queries.length), embR φ (gs sx m) =
      storedX (AspisV5ComponentCConcreteFoldLinearity.childIndex (raw.queries.get ⟨m / 4, by omega⟩) ⟨m % 4, by omega⟩))
    (hsy : ∀ (m : ℕ) (hm : m < 4 * raw.queries.length), embR φ (gs sy m) =
      storedY (AspisV5ComponentCConcreteFoldLinearity.childIndex (raw.queries.get ⟨m / 4, by omega⟩) ⟨m % 4, by omega⟩))
    (hselC : ∀ (c : Fin 16) (t : Fin (24 + 4 * raw.queries.length)),
      (sel1 c t).val = gNL sel1a (c.val * (24 + 4 * raw.queries.length) + t.val))
    (hselHv : ∀ t : Fin (24 + 16 * raw.queries.length),
      ((selH t).1).val = gNL selha t.val / 4 ∧ ((selH t).2).val = gNL selha t.val % 4)
    (hloC : ∀ c : Fin 16, (toData pb ct).loff c.val = c.val * ((24 + 4 * raw.queries.length) * (24 + 4 * raw.queries.length)))
    (hloH : (toData pb ct).loff 16 = 16 * ((24 + 4 * raw.queries.length) * (24 + 4 * raw.queries.length)))
    (hblo : R1CertBuild.fill_lo al zz tr sx sy inact sel1a selha nqU = ok pb.lo) :
    P_R1 π B hB (decode B w raw) := by
  have hA : ∀ (j : ℕ) (hj : j < 10), Alimb B φ al j = alpha (decode B w raw) ⟨j, hj⟩ :=
    fun j hj => alimb_eq B φ w raw hup al hal ⟨j, hj⟩
  have hq : (decode B w raw).queries = raw.queries.toFinset := decode_queries B w raw
  obtain ⟨LC, LH⟩ := fill_lo_spec al zz tr sx sy inact sel1a selha hblo
  rw [hnqU] at LC LH
  refine check_sound' pb ct hc π B hB w raw φ hup hnq hz hrw src stO hOwn hRound hT al hal ha9 hbuild
    wb fp hcov hbw rows sel stG hRel hGOwn hGRound hGBat hnl sel1 hsel1 hlw1 ?_ selH hselH hlwH ?_
  · intro c i x
    obtain ⟨rr, ii, hrr, hii, hv⟩ := LC c.val c.2 i.val i.2 x.val x.2
    have e := c1_entry_ident (Bat := R1Bat) B φ hT hB π (decode B w raw) (Fin.castLE (by omega) c)
      raw.queries hq al zz tr sx sy inact hA hzx hzy htr hin hsx hsy (sel1 c x) (hsel1 c x).2 rr ii
      (by rw [hrr, ← hselC c x]) i hii hv
    show flatC1 B hB raw.queries _ i = _
    rw [e]
    show φ _ = φ (gs (sl pb.lo) _)
    rw [show (toData pb ct).loff c.val = _ from hloC c]
    rfl
  · intro i x
    obtain ⟨rr, kk, ii, hrr, hkk, hii, hv⟩ := LH i.val i.2 x.val x.2
    have e := h1_entry_ident (Bat := R1Bat) B φ hT hB π (decode B w raw) raw.queries hq al zz tr sx sy
      inact hA hzx hzy htr hin hsx hsy (selH x).1 (hselH x).1 (selH x).2 rr kk ii
      (by rw [hrr, (hselHv x).1]) (by rw [hkk, (hselHv x).2]) i hii hv
    show flatH1 B hB raw.queries _ i = _
    rw [e]
    show φ _ = φ (gs (sl pb.lo) _)
    rw [show (toData pb ct).loff 16 = _ from hloH]
    rfl

#print axioms check_sound''

end R1Z.CertCheckSound

end
