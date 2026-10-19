import R1Z.CertCheckSound3
import R1Z.CertOwnEntries
import R1Z.CertOwnBlock

/-! D62: **`check_sound'''`** — `check_sound''` with the own identifications
`hOwn` and `hGOwn` discharged by the extracted own-column builder `fill_own`
(`hbo`, `hbg`): the QPrime sources are the Lean tapes `srcOf` of the Rust source
descriptors (lane, row, limb), the G sources `gSrc (sel t)`, the block starts
`stOf` (G block at `10·wB`).  New premises: descriptor bounds (`hrow`, `hlimbB`,
`hlane`, `hgrow`), the block widths (`hwl`, `hgwl`), the G family layout
(`hgk`, `hselG`, `hglane`) and the column strides (`hos`, `hgw`). -/

set_option autoImplicit false

noncomputable section

namespace R1Z.CertCheckSound

open scoped BigOperators
open Aeneas Aeneas.Std Result R1CertCheck R1Z.CertCheck R1Z.CertBuild R1Z.CertOwn
open R0P R0Z.MaskLayout R0Z.HonestView R0Z.Partition R0Z.K4
open R1Z.Batched R1Z.VerifierRelationsR1 R1Z.PredicateR1 R1Z.CertSound R1Z.CertR1
open R1Z.RfDec R1Z.RfSrc R1Z.RfChain R1Z.RfOwnLimb R1Z.RfBat R1Z.CertData R1Z.RfOwn R1Z.RfObs

attribute [local instance] Classical.propDecidable

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K] {F : Subfield K}

/-- The Lean tape of referenced source `t` (lane, row, limb descriptors). -/
def srcOf (lane srow slimb : Slice U32) (t : ℕ) : M K F :=
  R1Z.CertOwn.mkSrc (gNL lane t) ⟨gNL srow t % 1024, Nat.mod_lt _ (by norm_num)⟩
    ⟨gNL slimb t % 4, Nat.mod_lt _ (by norm_num)⟩

variable (pb : Pub) (ct : Cert)

/-- **`check_sound'''`**. -/
theorem check_sound''' (hc : check pb ct = ok true) (π : Fin 1024 ≃ Fin 1024) (B : PackBasis F) (hB : PackField B)
    (w : K) (raw : RawChallenges K F) (φ : R1Z.CertData.ZP →+* ↥F) (srow slimb : Slice U32)
    -- decoder facts
    (hup : ∀ (i : Fin 25) (k : Fin 4), raw.sem i (Fin.natAdd 4 k) = 0)
    (hnq : raw.queries.length = (toData pb ct).nq)
    (hz : ∀ j, (raw.circle j).1.1 ∈ K4 B hB ∧ (raw.circle j).1.2 ∈ K4 B hB)
    (hrw : (toData pb ct).rw = 1084)
    -- QPrime builder identifications
    (hRound : ∀ (i : Fin 1084) (t : Fin (toData pb ct).N),
      flat B hB (z4c (R0Z.Z4Maps.roundMaskMap (Bat := R1Bat) π B (decode B w raw) (srcOf (sl pb.lane) srow slimb t))) i =
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
    (rows : Fin (toData pb ct).q → R1Rel × Fin 8) (sel : Fin (toData pb ct).NG → Fin 1024 × Fin 4)
    (hRel : ∀ (x : Fin (toData pb ct).q) (c : Fin ((78 + nf) * 8)),
      relMat wb π (decode B w raw) fp rows x c = φ (rowM (toData pb ct).rel (toData pb ct).bw x c))
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
    (hgwl : gi (sl pb.gwl) 0 = wE raw.queries.length) :
    P_R1 π B hB (decode B w raw) := by
  have hA : ∀ (j : ℕ) (hj : j < 10), Alimb B φ al j = alpha (decode B w raw) ⟨j, hj⟩ :=
    fun j hj => alimb_eq B φ w raw hup al hal ⟨j, hj⟩
  have hq : (decode B w raw).queries = raw.queries.toFinset := decode_queries B w raw
  have hnq' : nqU.val = raw.queries.length := hnqU
  refine check_sound'' pb ct hc π B hB w raw φ hup hnq hz hrw (fun t => srcOf (sl pb.lane) srow slimb t.val)
    (stOf raw.queries.length) ?_ hRound hT al hal ha9 hbuild wb fp hcov hbw rows sel
    (fun _ => 10 * wB raw.queries.length) hRel ?_ hGRound hGBat hnl sel1 hsel1 hlw1 selH hselH hlwH
    zz tr sx sy inact sel1a selha nqU hnqU hzx hzy htr hin hsx hsy hselC hselHv hloC hloH hblo
  · intro p t
    have ht := t.2
    obtain ⟨hr1, hr2⟩ := hrow t.val ht
    have hl4 := hlimbB t.val ht
    have hj := hlane t.val ht
    have hrv : (⟨gNL srow t.val % 1024, Nat.mod_lt _ (by norm_num)⟩ : Fin 1024).val = gNL srow t.val :=
      Nat.mod_eq_of_lt hr2
    have hkv : (⟨gNL slimb t.val % 4, Nat.mod_lt _ (by norm_num)⟩ : Fin 4).val = gNL slimb t.val :=
      Nat.mod_eq_of_lt hl4
    have hr0 : (⟨gNL srow t.val % 1024, Nat.mod_lt _ (by norm_num)⟩ : Fin 1024) ≠ 0 := fun h => by
      have := congrArg Fin.val h
      rw [hrv] at this
      simp at this
      omega
    exact own_src_ident (Bat := R1Bat) B φ hB π (decode B w raw) raw.queries (toData pb ct).own
      (toData pb ct).os (toData pb ct).lane (toData pb ct).wl (stOf raw.queries.length) t.val
      (gi (sl pb.lane) t.val) hj _ hr0 _ rfl (hwl _ hj)
      (fun hk c i => by
        rw [own_hC (Bat := R1Bat) B φ hT hB π (decode B w raw) raw.queries hq al zz tr sx sy inact (sl pb.lane)
          srow slimb hA hzx hzy htr hin hsx hsy hnq' (by rw [hosU]; exact hos) hbo t.val (by rw [hnU]; exact ht)
          hk _ hr0 hrv.symm c i, hosU]
        rfl)
      (fun hk c i => by
        rw [own_hE (Bat := R1Bat) B φ hT hB π (decode B w raw) raw.queries hq al zz tr sx sy inact (sl pb.lane)
          srow slimb hA hzx hzy htr hin hsx hsy hnq' (by rw [hosU]; exact hos) hbo t.val (by rw [hnU]; exact ht)
          hk _ hr0 hrv.symm _ hkv.symm c i, hosU]
        rfl) p
  · intro p t
    have ht := t.2
    obtain ⟨hs1, hs2⟩ := hselG t
    have hr0 : (sel t).1 ≠ 0 := fun h => by
      have := hgrow t.val ht
      rw [← hs1, h] at this
      simp at this
    have hmk : gSrc (K := K) (F := F) (sel t).1 (sel t).2 = R1Z.CertOwn.mkSrc 10 (sel t).1 (sel t).2 := by
      simp [R1Z.CertOwn.mkSrc]
    rw [hmk]
    exact own_src_ident (Bat := R1Bat) B φ hB π (decode B w raw) raw.queries (toData pb ct).gown
      (toData pb ct).gw (toData pb ct).glane (toData pb ct).gwl (fun _ => 10 * wB raw.queries.length) t.val
      10 (by norm_num) _ hr0 _ (by simp [stOf]) (by
        show gi (sl pb.gwl) (gi (sl pb.glane) t.val) = _
        rw [hglane t.val ht, hgwl]
        simp)
      (fun hk => absurd hk (by norm_num))
      (fun _ c i => by
        rw [own_hE (Bat := R1Bat) B φ hT hB π (decode B w raw) raw.queries hq al zz tr sx sy inact gk
          gsrow gslimb hA hzx hzy htr hin hsx hsy hnq' (by rw [hgwU]; exact hgw) hbg t.val (by rw [hgnU]; exact ht)
          (by rw [hgk t.val ht]) _ hr0 hs1.symm _ hs2.symm c i, hgwU]
        rfl) p

#print axioms check_sound'''

end R1Z.CertCheckSound

end
