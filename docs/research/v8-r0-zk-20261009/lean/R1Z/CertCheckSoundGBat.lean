import R1Z.CertCheckSoundRound
import R1Z.CertGBatIdent

/-! D59.2 / D64.2: **`check_sound_gbat`**: `check_sound_round` with the G batched
identification `hGBat` discharged by `CertRel.gbat_ident` (CertGBatIdent): every support cell of
every G source's batched image is the Rust `unit_functionals` model `gbatP`, with the inputs of the
relation builder (`Alimb al`, `Alimb zz`, `gN tr`, `gN ti`, `flK inact`, the openings `Wl op`,
the quarter) under its premises (`alimb_eq`, `hzx`, `hzy`, `htr`, `hin`, `hti`, `hop`).
New premises: the stored first-line points `X18` at the opened folded positions (`hX18`, an
input table under a named premise, D59.2 ruling), `hfo` (every listed folded position is opened)
and the column entries `hGBent` (`pb.gbat`: the eight WideExact limbs of cell `c` of column `t`
combine, in the basis `wb`, to the model value).  Compile in env J. -/

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

/-- **`check_sound_gbat`**: `check_sound''''` without `hz`, `hRound`, `hGRound`, `hGBat`. -/
theorem check_sound_gbat (hc : check pb ct = ok true) (π : Fin 1024 ≃ Fin 1024) (B : PackBasis F) (hB : PackField B)
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
        srcRoundR (Alimb B φ al) (gN tr) (flK φ inact) B.i B.u 10 (sel t).1.val (sel t).2.val p.val) 
    -- G batched columns (replace hGBat): stored first-line points, opened positions, column entries
    (X18 : ℕ → K)
    (hX18 : ∀ f : Fin nf, X18 f.val = algebraMap (ZMod AspisCircleGroupOrder.P) K
      (AspisV7ExactOneFoldDomains.storedFirstLineX18 (fp f)))
    (hfo : ∀ f : Fin nf, FoldedOpen (decode B w raw) (fp f))
    (hGBent : ∀ (t : Fin (toData pb ct).NG) (c : Fin (78 + nf)),
      ∑ l : Fin 8, φ ((toData pb ct).gbat (t.val * (toData pb ct).bw + (8 * c.val + l.val))) • wb l =
        R1Z.CertRel.gbatP (Alimb B φ al) (Alimb B φ zz) (gN tr) (gN ti) (flK φ inact) (Wl B φ w op 0)
          (Wl B φ w op 1) (Wl B φ w op 2) (Wl B φ w op 3) (embR φ 536870912) B.i B.u X18 nf
          (sel t).1.val (sel t).2.val c.val) :
    P_R1 π B hB (decode B w raw) := by
  have hA : ∀ (n : ℕ) (h : n < 10), Alimb B φ al n = alpha (decode B w raw) ⟨n, h⟩ :=
    fun n h => alimb_eq B φ w raw hup al hal ⟨n, h⟩
  have hFl : ∀ r : Fin 1024, flK φ inact r.val = if r ∈ copyInactiveRows then 1 else 0 :=
    fun r => embR_flag φ inact r (hin r)
  have hsel0 : ∀ t, (sel t).1 ≠ 0 := fun t h => by
    obtain ⟨hs1, -⟩ := hselG t
    have := hgrow t.val t.2
    rw [← hs1, h] at this
    simp at this
  refine check_sound_round pb ct hc π B hB w raw φ srow slimb hup hnq hrw hT al hal ha9 hbuild wb fp hcov hbw sel
    (R1Z.CertRel.gbat_ident π B (decode B w raw) (Alimb B φ al) (Alimb B φ zz) (gN tr) (gN ti) (flK φ inact)
      hA hzx hzy htr hFl hti (Wl B φ w op 0) (Wl B φ w op 1) (Wl B φ w op 2) (Wl B φ w op 3)
      (embR φ 536870912) (hop 0) (hop 1) (hop 2) (hop 3) (e_quarter _) wb fp X18 hX18 hfo φ sel hsel0
      (toData pb ct).gbat (toData pb ct).bw hGBent) hnl sel1 hsel1 hlw1 selH hselH hlwH zz tr sx sy inact sel1a selha nqU hnqU hzx hzy htr hin hsx hsy hselC hselHv hloC hloH hblo nU osU hnU hosU hos hbo hrow hlimbB hlane hwl gk gsrow gslimb gnU gwU hgnU hgwU hgw hbg hgk hselG hgrow hglane hgwl hW hwb ti op fpos rk ru li x16 nfU qU hnfU hqU hbr hti hop hfp hinj hru hrq hl0 hl1 hl2 hx16 hRent hGent

#print axioms check_sound_gbat

end R1Z.CertCheckSound

end
