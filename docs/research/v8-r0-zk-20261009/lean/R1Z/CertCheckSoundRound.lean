import R1Z.CertCheckSound5
import R1Z.CertRoundIdent

/-! D59.2 / D62.3 / D64.2: **`check_sound_round`**: `check_sound''''` with the pure-round
identifications `hRound`, `hGRound` and the decoder fact `hz` discharged.

* `hRound`, `hGRound`: by `CertRound.z4c_srcTape` (CertRoundIdent) the Z4c coordinates of every
  QPrime source `srcOf …` and every G source `gSrc (sel t)` are the Rust `round_row`/`tail_row`
  model `srcRoundR`, with the alpha challenges `Alimb al` (`alimb_eq`), the transport `gN tr`
  (`htr`) and the inactive flags `flK inact` (`hin`), the same inputs and premises as the lift,
  own and relation builders.  The new premises are the column entries: `hRent` (`pb.round`) and
  `hGent` (`pb.ground`): the four limbs of coordinate `p` of column `t` pack to the model value.
* `hz`: the OOD coordinates are `Alimb zz` values (`hzx`, `hzy`, already premises of the lift
  builder), i.e. `pack4` of base-field limbs, hence in `K₄`.

This module only composes; compile in env J. -/

set_option autoImplicit false

noncomputable section

namespace R1Z.CertCheckSound

open scoped BigOperators
open Aeneas Aeneas.Std Result R1CertCheck R1Z.CertCheck R1Z.CertBuild R1Z.CertOwn
open R0P R0Z.MaskLayout R0Z.HonestView R0Z.Partition R0Z.K4
open R1Z.Batched R1Z.VerifierRelationsR1 R1Z.PredicateR1 R1Z.CertSound R1Z.CertR1
open R1Z.RfDec R1Z.RfSrc R1Z.RfChain R1Z.RfOwnLimb R1Z.RfBat R1Z.CertData R1Z.RfOwn R1Z.RfObs R1Z.CertRel

open R1Z.CertRound

attribute [local instance] Classical.propDecidable

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K] {F : Subfield K}

variable (pb : Pub) (ct : Cert)

theorem alimb_mem_K4 (B : PackBasis F) (hB : PackField B) (φ : R1Z.CertData.ZP →+* ↥F) (s : Slice U32) (n : ℕ) :
    Alimb B φ s n ∈ K4 B hB := by
  unfold Alimb
  rw [psi4_pack4]
  exact (mem_K4_iff_pack4 B hB).2 ⟨_, fun j => (φ _).2, rfl⟩

/-- **`check_sound_round`**: `check_sound''''` without `hz`, `hRound`, `hGRound`. -/
theorem check_sound_round (hc : check pb ct = ok true) (π : Fin 1024 ≃ Fin 1024) (B : PackBasis F) (hB : PackField B)
    (w : K) (raw : RawChallenges K F) (φ : R1Z.CertData.ZP →+* ↥F) (srow slimb : Slice U32)
    -- decoder facts
    (hup : ∀ (i : Fin 25) (k : Fin 4), raw.sem i (Fin.natAdd 4 k) = 0)
    (hnq : raw.queries.length = (toData pb ct).nq)
    (hrw : (toData pb ct).rw = 1084)
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
    (sel : Fin (toData pb ct).NG → Fin 1024 × Fin 4)
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
    (hblo : R1CertBuild.fill_lo al zz tr sx sy inact sel1a selha nqU = ok pb.lo)
    -- own-column builder (replaces hOwn and hGOwn)
    (nU osU : Usize) (hnU : nU.val = (toData pb ct).N) (hosU : osU.val = pb.os.val)
    (hos : 24 + 16 * raw.queries.length ≤ pb.os.val)
    (hbo : R1CertBuild.fill_own al zz tr sx sy inact (sl pb.lane) srow slimb nU osU nqU = ok pb.own)
    (hrow : ∀ t, t < (toData pb ct).N → 1 ≤ gNL srow t ∧ gNL srow t < 1024)
    (hlimbB : ∀ t, t < (toData pb ct).N → gNL slimb t < 4)
    (hlane : ∀ t, t < (toData pb ct).N → gi (sl pb.lane) t < 12)
    (hwl : ∀ j, j < 12 → gi (sl pb.wl) j = if j < 10 then wB raw.queries.length else wE raw.queries.length)
    (gk gsrow gslimb : Slice U32) (gnU gwU : Usize) (hgnU : gnU.val = (toData pb ct).NG) (hgwU : gwU.val = pb.gw.val)
    (hgw : 24 + 16 * raw.queries.length ≤ pb.gw.val)
    (hbg : R1CertBuild.fill_own al zz tr sx sy inact gk gsrow gslimb gnU gwU nqU = ok pb.gown)
    (hgk : ∀ t, t < (toData pb ct).NG → gNL gk t = 10)
    (hselG : ∀ t : Fin (toData pb ct).NG, ((sel t).1).val = gNL gsrow t.val ∧ ((sel t).2).val = gNL gslimb t.val)
    (hgrow : ∀ t, t < (toData pb ct).NG → 1 ≤ gNL gsrow t)
    (hglane : ∀ t, t < (toData pb ct).NG → gi (sl pb.glane) t = 0)
    (hgwl : gi (sl pb.gwl) 0 = wE raw.queries.length)
    -- relation builder (replaces hRel): the WideExact model, the builder run, inputs under named premises
    (hW : w * w = B.u) (hwb : ∀ k : Fin 8, wb k = wbP B.i B.u w k.val)
    (ti op fpos rk ru li x16 : Slice U32) (nfU qU : Usize) (hnfU : nfU.val = nf) (hqU : qU.val = (toData pb ct).q)
    (hbr : R1CertBuild.fill_rel al zz tr inact ti op fpos rk ru li x16 nfU qU = ok pb.rel)
    (hti : ∀ j : Fin 1024, gN ti j.val = (π.symm j).val)
    (hop : ∀ o : Fin 4, Wl B φ w op o.val = raw.opening o)
    (hfp : ∀ f : Fin nf, (fp f).val = gN fpos f.val) (hinj : Function.Injective fp)
    (hru : ∀ ρ, gN ru ρ < 262144)
    (hrq : ∀ ρ, 8 * ρ < (toData pb ct).q → 3 ≤ gN rk ρ →
      (⟨gN ru ρ % 262144, Nat.mod_lt _ (by decide)⟩ : Fin 262144) ∈ raw.queries)
    (hl0 : ∀ ρ, 8 * ρ < (toData pb ct).q → 4 ≤ gN rk ρ → embR φ (gs li (3 * ρ)) =
      algebraMap (ZMod AspisCircleGroupOrder.P) K
        (R1Z.BatchedAlgebra.lineInverse ⟨gN ru ρ / 4, by have := hru ρ; omega⟩ 0))
    (hl1 : ∀ ρ, 8 * ρ < (toData pb ct).q → 4 ≤ gN rk ρ → embR φ (gs li (3 * ρ + 1)) =
      algebraMap (ZMod AspisCircleGroupOrder.P) K
        (R1Z.BatchedAlgebra.lineInverse ⟨gN ru ρ / 4, by have := hru ρ; omega⟩ 1))
    (hl2 : ∀ ρ, 8 * ρ < (toData pb ct).q → 4 ≤ gN rk ρ → embR φ (gs li (3 * ρ + 2)) =
      algebraMap (ZMod AspisCircleGroupOrder.P) K
        (R1Z.BatchedAlgebra.lineInverse ⟨gN ru ρ / 4, by have := hru ρ; omega⟩ 2))
    (hx16 : ∀ ρ, 8 * ρ < (toData pb ct).q → 4 ≤ gN rk ρ → embR φ (gs x16 ρ) =
      algebraMap (ZMod AspisCircleGroupOrder.P) K
        (AspisV5FriReleasedLineGeometry.storedLine16X ⟨gN ru ρ / 4, by have := hru ρ; omega⟩)) 
    -- pure-round columns (replace hRound and hGRound): the column entries are the Rust model
    (hRent : ∀ (t : Fin (toData pb ct).N) (p : Fin 271),
      pack4 B (fun l : Fin 4 => ((φ ((toData pb ct).round (t.val * (toData pb ct).rw + (4 * p.val + l.val))) : F) : K)) =
        srcRoundR (Alimb B φ al) (gN tr) (flK φ inact) B.i B.u (gNL (sl pb.lane) t.val) (gNL srow t.val)
          (gNL slimb t.val) p.val)
    (hGent : ∀ (t : Fin (toData pb ct).NG) (p : Fin 271),
      pack4 B (fun l : Fin 4 => ((φ ((toData pb ct).ground (t.val * (toData pb ct).rw + (4 * p.val + l.val))) : F) : K)) =
        srcRoundR (Alimb B φ al) (gN tr) (flK φ inact) B.i B.u 10 (sel t).1.val (sel t).2.val p.val) :
    P_R1 π B hB (decode B w raw) := by
  have hA : ∀ (n : ℕ) (h : n < 10), Alimb B φ al n = alpha (decode B w raw) ⟨n, h⟩ :=
    fun n h => alimb_eq B φ w raw hup al hal ⟨n, h⟩
  have hFl : ∀ r : Fin 1024, flK φ inact r.val = if r ∈ copyInactiveRows then 1 else 0 :=
    fun r => embR_flag φ inact r (hin r)
  have hz : ∀ j, (raw.circle j).1.1 ∈ K4 B hB ∧ (raw.circle j).1.2 ∈ K4 B hB := fun j =>
    ⟨by rw [← hzx j]; exact alimb_mem_K4 B hB φ zz _, by rw [← hzy j]; exact alimb_mem_K4 B hB φ zz _⟩
  refine check_sound'''' pb ct hc π B hB w raw φ srow slimb hup hnq hz hrw ?_ hT al hal ha9 hbuild wb fp hcov hbw sel ?_ hGBat hnl sel1 hsel1 hlw1 selH hselH hlwH zz tr sx sy inact sel1a selha nqU hnqU hzx hzy htr hin hsx hsy hselC hselHv hloC hloH hblo nU osU hnU hosU hos hbo hrow hlimbB hlane hwl gk gsrow gslimb gnU gwU hgnU hgwU hgw hbg hgk hselG hgrow hglane hgwl hW hwb ti op fpos rk ru li x16 nfU qU hnfU hqU hbr hti hop hfp hinj hru hrq hl0 hl1 hl2 hx16
  · intro i t
    have ht := t.2
    obtain ⟨hr1, hr2⟩ := hrow t.val ht
    have hl4 := hlimbB t.val ht
    have hr0 : (⟨gNL srow t.val % 1024, Nat.mod_lt _ (by norm_num)⟩ : Fin 1024) ≠ 0 := fun h => by
      have := congrArg Fin.val h
      simp only [Fin.val_zero] at this
      rw [Nat.mod_eq_of_lt hr2] at this
      omega
    have hs : srcOf (K := K) (F := F) (sl pb.lane) srow slimb t.val =
        srcTape (gNL (sl pb.lane) t.val) ⟨gNL srow t.val % 1024, Nat.mod_lt _ (by norm_num)⟩
          ⟨gNL slimb t.val % 4, Nat.mod_lt _ (by norm_num)⟩ := rfl
    rw [hs, z4c_srcTape π B (decode B w raw) (Alimb B φ al) hA (gN tr) htr (flK φ inact) hFl _ _ hr0]
    refine flat_of_pack B hB φ _ _ t.val _ (fun p => ?_) i
    have e := hRent t p
    rw [← Nat.mod_eq_of_lt hr2, ← Nat.mod_eq_of_lt hl4] at e
    exact e
  · intro i t
    have ht := t.2
    obtain ⟨hs1, hs2⟩ := hselG t
    have hr0 : (sel t).1 ≠ 0 := fun h => by
      have := hgrow t.val ht
      rw [← hs1, h] at this
      simp at this
    have hs : gSrc (K := K) (F := F) (sel t).1 (sel t).2 = srcTape 10 (sel t).1 (sel t).2 := rfl
    rw [hs, z4c_srcTape π B (decode B w raw) (Alimb B φ al) hA (gN tr) htr (flK φ inact) hFl _ _ hr0]
    exact flat_of_pack B hB φ _ _ t.val _ (hGent t) i

#print axioms alimb_mem_K4
#print axioms check_sound_round

end R1Z.CertCheckSound

end
