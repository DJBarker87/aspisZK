import R1Z.CertCheckSoundGBat
import R1Z.CertRoundFill
import R1Z.CertGBatFill

/-! D72.2: **`check_sound_cols`**: `check_sound_gbat` with the column-entry premises `hRent`
(`pb.round`), `hGent` (`pb.ground`) and `hGBent` (`pb.gbat`) discharged by the extracted column
writers.  `fill_round_entries` (CertRoundFill) gives every packed round entry as the CertRoundK
model `srcRoundR` of the run's descriptors, `fill_gbat_entries` (CertGBatFill) every G batched cell
as the CertGBatK model `gbatP`.  The stored first-line points `X18` become the writer's input limbs
`x18` under the named premise `hx18` (D59.2 ruling).  The descriptors are the own-column builder's
(`sl pb.lane`, `srow`, `slimb`; `gk`, `gsrow`, `gslimb`), so their premises (`hgk`, `hselG`) are
reused.  Composition only, core tactics only; compile in env J. -/

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

/-- **`check_sound_cols`**: `check_sound_gbat` without `hRent`, `hGent`, `X18`/`hX18` and `hGBent`. -/
theorem check_sound_cols (hc : check pb ct = ok true) (π : Fin 1024 ≃ Fin 1024) (B : PackBasis F) (hB : PackField B)
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
    -- column writers (replace hRent, hGent, X18/hX18, hGBent): the extracted builders' runs; the
    -- stored first-line points of the folded positions are the input limbs x18 (named premise hx18)
    (hbr5 : R1CertBuild.fill_round al tr inact (sl pb.lane) srow slimb nU = ok pb.round)
    (hbg5 : R1CertBuild.fill_round al tr inact gk gsrow gslimb gnU = ok pb.ground)
    (x18 : Slice U32)
    (hx18 : ∀ f : Fin nf, embR φ (gs x18 f.val) = algebraMap (ZMod AspisCircleGroupOrder.P) K
      (AspisV7ExactOneFoldDomains.storedFirstLineX18 (fp f)))
    (hfo : ∀ f : Fin nf, FoldedOpen (decode B w raw) (fp f))
    (hbg6 : R1CertBuild.fill_gbat al zz tr inact ti op x18 gsrow gslimb gnU nfU = ok pb.gbat) :
    P_R1 π B hB (decode B w raw) :=
  check_sound_gbat pb ct hc π B hB w raw φ srow slimb hup hnq hrw hT al hal ha9 hbuild wb fp hcov hbw sel hnl
    sel1 hsel1 hlw1 selH hselH hlwH zz tr sx sy inact sel1a selha nqU hnqU hzx hzy htr hin hsx hsy hselC hselHv
    hloC hloH hblo nU osU hnU hosU hos hbo hrow hlimbB hlane hwl gk gsrow gslimb gnU gwU hgnU hgwU hgw hbg hgk
    hselG hgrow hglane hgwl hW hwb ti op fpos rk ru li x16 nfU qU hnfU hqU hbr hti hop hfp hinj hru hrq hl0 hl1
    hl2 hx16
    (fun t p => by
      rw [hrw]
      exact fill_round_entries B φ al tr inact (sl pb.lane) srow slimb hT hbr5 t.val p.val (by rw [hnU]; exact t.2) p.2)
    (fun t p => by
      have e := fill_round_entries B φ al tr inact gk gsrow gslimb hT hbg5 t.val p.val (by rw [hgnU]; exact t.2) p.2
      rw [hgk t.val t.2] at e
      rw [hrw, (hselG t).1, (hselG t).2]
      exact e)
    (fun m => embR φ (gs x18 m)) hx18 hfo
    (fun t c => by
      have e := fill_gbat_entries B φ w al zz tr inact ti op x18 gsrow gslimb hT hW wb hwb hbg6 t.val c.val
        (by rw [hgnU]; exact t.2) (by rw [hnfU]; exact c.2)
      rw [hnfU] at e
      rw [hbw, (hselG t).1, (hselG t).2]
      exact e)

#print axioms check_sound_cols

end R1Z.CertCheckSound

end
