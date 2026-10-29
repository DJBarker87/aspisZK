import R1Z.EventsR1P2Bin

-- Binary-format copy of `R1Z.EventsR1P3` (LOG D76): the text is unchanged except that it is
-- built over `GamesR1PBin` / `LayoutR1P*Bin` (binary node index and `0x12 ‖ 2 children`).

/-! Events and freshness, part 3 (DESIGN-R1-REAL §5): `HitFresh` for every
position (`hit_tr`, `hit_cm`) and `PairFresh` for every pair of distinct
positions (`pair_all`). -/
set_option autoImplicit false
noncomputable section
namespace R1Z.EventsR1PBin
open R0P R0Z R0Z.JointView R0Z.FsStatement R0Z.FsAbort R0Z.FsAbortBounds R0Z.HvzkV
  R1Z.Batched R1Z.LensR1 R1Z.TranscriptR1 R1Z.GamesR1 R1Z.LazyFrozen R1Z.GamesR1PBin
  R1Z.CouplingR1PBin R1Z.LayoutR1PBin
attribute [local instance] Classical.propDecidable

variable {K CommitHandle Aux : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K] {F : Subfield K}

section Blocks
variable (W : R1Wire K CommitHandle Aux) (Pr : R1ProverP K CommitHandle Aux F W)

theorem tapeR_tame {U : Type} (L : Lens (AttS (F := F) W Pr) U) (hL : Tame W Pr L)
    (a : AttS (F := F) W Pr) (u : U) : tapeR W Pr (L.set a u).2.1 = tapeR W Pr a.2.1 := by
  unfold tapeR
  rw [hL.e₁, hL.e₂]

theorem restOf_vL_rest (q : RIdx) (a : AttS (F := F) W Pr) (u : OracleAnswer) :
    restOf ((vL W Pr (.inr (.inr (.inr q)))).set a u).2.1 = Function.update (restOf a.2.1) q u := by
  funext q'
  by_cases hq : q' = q
  · subst hq
    simp [vL, restOf]
  · simp [vL, restOf, Function.update_of_ne hq]

theorem trOf_vL_rest (q : RIdx) (a : AttS (F := F) W Pr) (u : OracleAnswer) :
    trOf ((vL W Pr (.inr (.inr (.inr q)))).set a u).2.1 = trOf a.2.1 := by
  funext j
  simp [vL, trOf]

theorem rootsOf_vL_rest (q : RIdx) (a : AttS (F := F) W Pr) (u : OracleAnswer) :
    rootsOf ((vL W Pr (.inr (.inr (.inr q)))).set a u).2.1 = rootsOf a.2.1 := by
  funext i
  simp [vL, rootsOf]

theorem restOf_chain (c : Coord) (a : AttS (F := F) W Pr) (u : OracleAnswer) :
    restOf ((chainL W Pr c).set a u).2.1 = restOf a.2.1 := by
  funext q
  cases c <;> simp [chainL, vL, selL, restOf]

theorem sec_chain (c : Coord) (a : AttS (F := F) W Pr) (u : OracleAnswer) :
    ((chainL W Pr c).set a u).1 = a.1 := by
  cases c <;> rfl

end Blocks

section Fresh
variable (W : R1Wire K CommitHandle Aux) (Pr : R1ProverP K CommitHandle Aux F W) (R : RomModel W)
  (eCm : W.Cm ≃ (RIdx → OracleAnswer)) (N : ℕ) (hN : 0 < N) (P : Challenges K → Prop)
  (h : HonestProver K) (V : Challenges K → h.Instance → Prop) (B : PackBasis F)
  (outputs : Statement K CommitHandle → Challenges K → Aux) (x : Statement K CommitHandle)
  (w : h.Instance) (adv : R1Adv K CommitHandle Aux)

theorem addrQ_cm (hb : RCommitBytes W Pr) (s : Fin N → AttS (F := F) W Pr) (k : Fin N)
    (c : CPos Pr.E₁ Pr.E₂) :
    addrQ W Pr R N hN h B outputs x w s (k, .inr c) =
      gram (W.pubBytes x) W.vtag (Pr.leafVal h w x (tapeR W Pr (s k).2.1) (chOf W (trOf (s k).2.1)))
        (s k).1 (dS W Pr R N hN x s) (restOf (s k).2.1) c :=
  hb _ _ _ _ _ _ _ _ _

theorem addrQ_other {U : Type} (L : Lens (AttS (F := F) W Pr) U) (hL : Tame W Pr L) (k : Fin N)
    (s : Fin N → AttS (F := F) W Pr) (u : U) (p : Fin N × Pos1 Pr.E₁ Pr.E₂) (hk : p.1 ≠ k) :
    addrQ W Pr R N hN h B outputs x w ((Lens.fnAt k L).set s u) p =
      addrQ W Pr R N hN h B outputs x w s p := by
  unfold addrQ
  rw [Lens.fnAt_set_ne _ _ _ _ _ hk, dS_tame W Pr R N hN x L hL]

theorem addrQ_tr_inv {U : Type} (L : Lens (AttS (F := F) W Pr) U) (hL : Tame W Pr L)
    (htr : ∀ a u, trOf (L.set a u).2.1 = trOf a.2.1) (hrt : ∀ a u, rootsOf (L.set a u).2.1 = rootsOf a.2.1)
    (k : Fin N) (s : Fin N → AttS (F := F) W Pr) (u : U) (k' : Fin N) (j : TRead) :
    addrQ W Pr R N hN h B outputs x w ((Lens.fnAt k L).set s u) (k', .inl j) =
      addrQ W Pr R N hN h B outputs x w s (k', .inl j) := by
  by_cases hk : k' = k
  · subst hk
    show addr j (recP W x (view h B outputs x w (chOf W (trOf (((Lens.fnAt k' L).set s u) k').2.1))
        (tapeR W Pr (((Lens.fnAt k' L).set s u) k').2.1)) (trOf (((Lens.fnAt k' L).set s u) k').2.1)
        (rootsOf (((Lens.fnAt k' L).set s u) k').2.1)) = _
    rw [Lens.fnAt_set_eq, htr, hrt, tapeR_tame W Pr L hL]
    rfl
  · exact addrQ_other W Pr R N hN h B outputs x w L hL k s u _ hk

theorem addrQ_cm_chain (c : Coord) (hc : ChainC c) (k : Fin N) (s : Fin N → AttS (F := F) W Pr)
    (u : OracleAnswer) (k' : Fin N) (c' : CPos Pr.E₁ Pr.E₂) :
    addrQ W Pr R N hN h B outputs x w ((Lens.fnAt k (chainL W Pr c)).set s u) (k', .inr c') =
      addrQ W Pr R N hN h B outputs x w s (k', .inr c') := by
  by_cases hk : k' = k
  · subst hk
    show Pr.caddr h w x (((Lens.fnAt k' (chainL W Pr c)).set s u) k').1
        (dS W Pr R N hN x ((Lens.fnAt k' (chainL W Pr c)).set s u))
        (tapeR W Pr (((Lens.fnAt k' (chainL W Pr c)).set s u) k').2.1)
        (restOf (((Lens.fnAt k' (chainL W Pr c)).set s u) k').2.1)
        (chOf W (trOf (((Lens.fnAt k' (chainL W Pr c)).set s u) k').2.1)) c' = _
    rw [dS_tame W Pr R N hN x _ (tame_chain W Pr c hc), Lens.fnAt_set_eq, sec_chain,
      tapeR_tame W Pr _ (tame_chain W Pr c hc), restOf_chain, (tame_chain W Pr c hc).ch]
    rfl
  · exact addrQ_other W Pr R N hN h B outputs x w _ (tame_chain W Pr c hc) k s u _ hk

theorem addrQ_sec_inv (hb : RCommitBytes W Pr) (i : Fin 3) (k : Fin N) (s : Fin N → AttS (F := F) W Pr)
    (z : NZ) (c' : CPos Pr.E₁ Pr.E₂) (hd : ¬ depS c' (.inl i)) :
    addrQ W Pr R N hN h B outputs x w ((Lens.fnAt k (secL W Pr i)).set s z) (k, .inr c') =
      addrQ W Pr R N hN h B outputs x w s (k, .inr c') := by
  rw [addrQ_cm W Pr R N hN h B outputs x w hb, addrQ_cm W Pr R N hN h B outputs x w hb,
    dS_tame W Pr R N hN x _ (tame_sec W Pr i), Lens.fnAt_set_eq]
  exact gram_sec_update _ _ _ _ _ _ _ _ _ hd

theorem addrQ_rest_inv (hb : RCommitBytes W Pr) (q : RIdx) (k : Fin N) (s : Fin N → AttS (F := F) W Pr)
    (u : OracleAnswer) (c' : CPos Pr.E₁ Pr.E₂) (hd : ¬ depS c' (.inr q)) :
    addrQ W Pr R N hN h B outputs x w ((Lens.fnAt k (vL W Pr (.inr (.inr (.inr q))))).set s u) (k, .inr c') =
      addrQ W Pr R N hN h B outputs x w s (k, .inr c') := by
  rw [addrQ_cm W Pr R N hN h B outputs x w hb, addrQ_cm W Pr R N hN h B outputs x w hb,
    dS_tame W Pr R N hN x _ (tame_rest W Pr q), Lens.fnAt_set_eq,
    tapeR_tame W Pr _ (tame_rest W Pr q), (tame_rest W Pr q).ch, restOf_vL_rest,
    show ((vL W Pr (.inr (.inr (.inr q)))).set (s k) u).1 = (s k).1 from rfl]
  convert gram_rest_update (W.pubBytes x) W.vtag
    (Pr.leafVal h w x (tapeR W Pr (s k).2.1) (chOf W (trOf (s k).2.1))) (s k).1
    (dS W Pr R N hN x s) (restOf (s k).2.1) q u c' hd

theorem fld_sec (hb : RCommitBytes W Pr) (k : Fin N) (c : CPos Pr.E₁ Pr.E₂) (i : Fin 3)
    (hs : src c = .inl i) (s : Fin N → AttS (F := F) W Pr) (z : NZ) :
    nzOf (fld (W.pubBytes x).length c
      (addrQ W Pr R N hN h B outputs x w ((Lens.fnAt k (secL W Pr i)).set s z) (k, .inr c))) = z := by
  rw [addrQ_cm W Pr R N hN h B outputs x w hb, fld_gram, hs]
  rw [Lens.fnAt_set_eq]
  show nzOf ((Function.update (s k).1 i z) i).1 = z
  rw [Function.update_self, nzOf_val]

theorem fld_rest (hb : RCommitBytes W Pr) (k : Fin N) (c : CPos Pr.E₁ Pr.E₂) (q : RIdx)
    (hs : src c = .inr q) (s : Fin N → AttS (F := F) W Pr) (u : OracleAnswer) :
    fld (W.pubBytes x).length c
      (addrQ W Pr R N hN h B outputs x w ((Lens.fnAt k (vL W Pr (.inr (.inr (.inr q))))).set s u)
        (k, .inr c)) = u := by
  rw [addrQ_cm W Pr R N hN h B outputs x w hb, fld_gram, hs, Lens.fnAt_set_eq, restOf_vL_rest]
  show Function.update (restOf (s k).2.1) q u q = u
  rw [Function.update_self]

/-- A commitment read's designated field is fresh against every address that
its lens does not move. -/
theorem cm_pf (hb : RCommitBytes W Pr) (k : Fin N) (c : CPos Pr.E₁ Pr.E₂)
    (fa : (Fin N → AttS (F := F) W Pr) → List UInt8)
    (hsec : ∀ i, src c = .inl i → ∀ s z, fa ((Lens.fnAt k (secL W Pr i)).set s z) = fa s)
    (hrest : ∀ q, src c = .inr q → ∀ s u,
      fa ((Lens.fnAt k (vL W Pr (.inr (.inr (.inr q))))).set s u) = fa s) :
    PairFresh fa (fun s => addrQ W Pr R N hN h B outputs x w s (k, .inr c)) (2 ^ 255) := by
  rcases hsrc : src c with i | q
  · exact pairFresh_of_lens (Lens.fnAt k (secL W Pr i)) fa _
      (fun a => nzOf (fld (W.pubBytes x).length c a)) _ card_NZ (hsec i hsrc)
      (fld_sec W Pr R N hN h B outputs x w hb k c i hsrc)
  · exact pairFresh_of_lens (Lens.fnAt k (vL W Pr (.inr (.inr (.inr q))))) fa _
      (fld (W.pubBytes x).length c) _ umin_le_card_ans (hrest q hsrc)
      (fld_rest W Pr R N hN h B outputs x w hb k c q hsrc)

theorem pub_of_opened (hop : ROpen Pr) (ch : Challenges K) (c : CPos Pr.E₁ Pr.E₂)
    (hc : openedC (Pr.openFib ch) c) : c ∈ (Pr.openList ch).map cposOf := by
  rcases c with T | (e | e) | q
  · exact List.mem_map.mpr ⟨.inl T, (hop.covers ch _).mpr trivial, rfl⟩
  · exact absurd hc id
  · exact absurd hc id
  · exact List.mem_map.mpr ⟨.inr q, (hop.covers ch _).mpr hc, rfl⟩

/-! ### Pair freshness -/

theorem pair_all (hb : RCommitBytes W Pr) (hE₁ : Pr.E₁ ≤ 2 ^ 64) (hE₂ : Pr.E₂ ≤ 2 ^ 64)
    (p p' : Fin N × Pos1 Pr.E₁ Pr.E₂) (hne : p ≠ p') :
    PairFresh (fun s => addrQ W Pr R N hN h B outputs x w s p)
        (fun s => addrQ W Pr R N hN h B outputs x w s p') (2 ^ 255) ∨
      PairFresh (fun s => addrQ W Pr R N hN h B outputs x w s p')
        (fun s => addrQ W Pr R N hN h B outputs x w s p) (2 ^ 255) := by
  have Fr := frameP W Pr h B outputs x w N
  obtain ⟨k, j | c⟩ := p <;> obtain ⟨k', j' | c'⟩ := p'
  · have hne' : (k, j) ≠ (k', j') := fun e => hne (by
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj e
      rfl)
    exact pairFresh_transcript (frameP W Pr h B outputs x w N) (k, j) (k', j') hne'
  · refine Or.inr (pairFresh_of_lens ((frameP W Pr h B outputs x w N).lens k (fc j)) _
      (taddr (frameP W Pr h B outputs x w N) k j) (extract j) _ umin_le_card_ans ?_
      (taddr_extract (frameP W Pr h B outputs x w N) k j))
    intro s u
    exact addrQ_cm_chain W Pr R N hN h B outputs x w (fc j) (chain_fc j) k s u k' c'
  · refine Or.inl (pairFresh_of_lens ((frameP W Pr h B outputs x w N).lens k' (fc j')) _
      (taddr (frameP W Pr h B outputs x w N) k' j') (extract j') _ umin_le_card_ans ?_
      (taddr_extract (frameP W Pr h B outputs x w N) k' j'))
    intro s u
    exact addrQ_cm_chain W Pr R N hN h B outputs x w (fc j') (chain_fc j') k' s u k c
  · by_cases hk : k = k'
    · subst hk
      have hc : c ≠ c' := fun e => hne (by rw [e])
      rcases fresh_or_sep hE₁ hE₂ c c' hc with h1 | h2 | h3
      · refine Or.inr (cm_pf W Pr R N hN h B outputs x w hb k c _ ?_ ?_)
        · intro i hi s z
          exact addrQ_sec_inv W Pr R N hN h B outputs x w hb i k s z c' (by rw [← hi]; exact h1)
        · intro q hq s u
          exact addrQ_rest_inv W Pr R N hN h B outputs x w hb q k s u c' (by rw [← hq]; exact h1)
      · refine Or.inl (cm_pf W Pr R N hN h B outputs x w hb k c' _ ?_ ?_)
        · intro i hi s z
          exact addrQ_sec_inv W Pr R N hN h B outputs x w hb i k s z c (by rw [← hi]; exact h2)
        · intro q hq s u
          exact addrQ_rest_inv W Pr R N hN h B outputs x w hb q k s u c (by rw [← hq]; exact h2)
      · refine Or.inl (pairFresh_of_ne _ _ _ (fun s => ?_))
        show addrQ W Pr R N hN h B outputs x w s (k, .inr c) ≠ addrQ W Pr R N hN h B outputs x w s (k, .inr c')
        rw [addrQ_cm W Pr R N hN h B outputs x w hb, addrQ_cm W Pr R N hN h B outputs x w hb]
        exact h3 _ _ _ _ _ _
    · refine Or.inr (cm_pf W Pr R N hN h B outputs x w hb k c _ ?_ ?_)
      · intro i _ s z
        exact addrQ_other W Pr R N hN h B outputs x w _ (tame_sec W Pr i) k s z (k', .inr c')
          (fun e => hk e.symm)
      · intro q _ s u
        exact addrQ_other W Pr R N hN h B outputs x w _ (tame_rest W Pr q) k s u (k', .inr c')
          (fun e => hk e.symm)

end Fresh

#print axioms tapeR_tame
#print axioms restOf_vL_rest
#print axioms addrQ_cm_chain
#print axioms addrQ_sec_inv
#print axioms addrQ_rest_inv
#print axioms fld_sec
#print axioms fld_rest
#print axioms cm_pf
#print axioms pub_of_opened
#print axioms pair_all
#print axioms trOf_vL_rest
#print axioms rootsOf_vL_rest
#print axioms restOf_chain
#print axioms sec_chain
#print axioms addrQ_cm
#print axioms addrQ_other
#print axioms addrQ_tr_inv
end R1Z.EventsR1PBin
