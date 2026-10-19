import R1Z.EventsR1P3Bin

-- Binary-format copy of `R1Z.EventsR1P4` (LOG D76): the text is unchanged except that it is
-- built over `GamesR1PBin` / `LayoutR1P*Bin` (binary node index and `0x12 ‖ 2 children`).

/-! Events and freshness, part 4 (DESIGN-R1-REAL §5): `HitFresh` for every
position.  A charged read's designated field is invisible to the middle
adversary: for an unaccepted attempt nothing of it is published; for an
unopened read of the accepted attempt, `hidden` + `RComLog` show the
verifier log does not move (`verLog_rest`). -/
set_option autoImplicit false
noncomputable section
namespace R1Z.EventsR1PBin
open R0P R0Z R0Z.JointView R0Z.FsStatement R0Z.FsAbort R0Z.FsAbortBounds R0Z.HvzkV
  R1Z.Batched R1Z.LensR1 R1Z.TranscriptR1 R1Z.GamesR1 R1Z.LazyFrozen R1Z.GamesR1PBin
  R1Z.CouplingR1PBin R1Z.LayoutR1PBin
attribute [local instance] Classical.propDecidable

variable {K CommitHandle Aux : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K] {F : Subfield K}

section Hit
variable (W : R1Wire K CommitHandle Aux) (Pr : R1ProverP K CommitHandle Aux F W) (R : RomModel W)
  (eCm : W.Cm ≃ (RIdx → OracleAnswer)) (N : ℕ) (hN : 0 < N) (P : Challenges K → Prop)
  (h : HonestProver K) (V : Challenges K → h.Instance → Prop) (B : PackBasis F)
  (outputs : Statement K CommitHandle → Challenges K → Aux) (x : Statement K CommitHandle)
  (w : h.Instance) (adv : R1Adv K CommitHandle Aux)

theorem qry_tame {U : Type} (L : Lens (AttS (F := F) W Pr) U) (hL : Tame W Pr L) (k : Fin N)
    (s : Fin N → AttS (F := F) W Pr) (u : U)
    (hv : accM W Pr eCm N P h V w s = some k →
      verLog W x (view h B outputs x w (drawW W ((toMP W Pr eCm s).1 k)) ((toMP W Pr eCm s).2 k))
          ((toMP W Pr eCm ((Lens.fnAt k L).set s u)).1 k) =
        verLog W x (view h B outputs x w (drawW W ((toMP W Pr eCm s).1 k)) ((toMP W Pr eCm s).2 k))
          ((toMP W Pr eCm s).1 k))
    (i : Fin W.qmax) :
    qryQ W Pr eCm N hN P h V B outputs x w adv i ((Lens.fnAt k L).set s u) =
      qryQ W Pr eCm N hN P h V B outputs x w adv i s := by
  unfold qryQ qryR
  rw [advLogR_congr W N hN P h V B outputs x w adv (toMP W Pr eCm s)
    (toMP W Pr eCm ((Lens.fnAt k L).set s u)) (accM_tame W Pr eCm N P h V w L hL k s u)
    (toMP_tame_tab W Pr eCm N L hL k s u ⟨0, hN⟩) ?_]
  intro k₀ hk₀
  refine ⟨toMP_tame_draw W Pr eCm N L hL k s u k₀, congrFun (toMP_tame_tape W Pr eCm N L hL k s u) k₀, ?_⟩
  by_cases hkk : k₀ = k
  · subst hkk
    exact hv hk₀
  · rw [toMP_tame_other W Pr eCm N L k s u k₀ hkk]

theorem hit_tr (k : Fin N) (j : TRead) (i : Fin W.qmax) :
    HitFresh (fun s => chargedQ W Pr eCm N P h V w s (k, .inl j))
      (qryQ W Pr eCm N hN P h V B outputs x w adv i)
      (fun s => addrQ W Pr R N hN h B outputs x w s (k, .inl j)) (2 ^ 255) := by
  refine hitFresh_transcript (frameP W Pr h B outputs x w N) k j _ _ ?_ ?_
  · intro s u hs
    exact (charged_tame W Pr eCm N P h V w (chainL W Pr (fc j)) (tame_chain W Pr (fc j) (chain_fc j))
      k s u (k, .inl j)).mpr hs
  · intro s u hs
    exact qry_tame W Pr eCm N hN P h V B outputs x w adv _ (tame_chain W Pr (fc j) (chain_fc j)) k s u
      (fun ha => absurd ha hs) i

theorem verLog_rest (hb : RCommitBytes W Pr) (hop : ROpen Pr)
    (hcom : RComLog W Pr eCm h B outputs x) (s : Fin N → AttS (F := F) W Pr) (k : Fin N)
    (c : CPos Pr.E₁ Pr.E₂) (q : RIdx) (hs : src c = .inr q) (hnp : ¬ pubC W Pr N s k c)
    (u : OracleAnswer) :
    verLog W x (view h B outputs x w (drawW W ((toMP W Pr eCm s).1 k)) ((toMP W Pr eCm s).2 k))
        ((toMP W Pr eCm ((Lens.fnAt k (vL W Pr (.inr (.inr (.inr q))))).set s u)).1 k) =
      verLog W x (view h B outputs x w (drawW W ((toMP W Pr eCm s).1 k)) ((toMP W Pr eCm s).2 k))
        ((toMP W Pr eCm s).1 k) := by
  have e1 : (toMP W Pr eCm ((Lens.fnAt k (vL W Pr (.inr (.inr (.inr q))))).set s u)).1 k =
      (trOf (s k).2.1, rootsOf (s k).2.1, eCm.symm (Function.update (restOf (s k).2.1) q u),
        (s k).2.2.2) := by
    show (gM W Pr eCm (((Lens.fnAt k (vL W Pr (.inr (.inr (.inr q))))).set s u) k)).1 = _
    rw [Lens.fnAt_set_eq]
    show (trOf _, rootsOf _, eCm.symm (restOf _), _) = _
    rw [trOf_vL_rest, rootsOf_vL_rest, restOf_vL_rest]
    rfl
  rw [e1]
  show tLog W x (view h B outputs x w (chOf W (trOf (s k).2.1)) ((toMP W Pr eCm s).2 k))
        (trOf (s k).2.1, rootsOf (s k).2.1, eCm.symm (Function.update (restOf (s k).2.1) q u), (s k).2.2.2) ++
      W.comLog (eCm.symm (Function.update (restOf (s k).2.1) q u)) (rootsOf (s k).2.1)
        (view h B outputs x w (chOf W (trOf (s k).2.1)) ((toMP W Pr eCm s).2 k)) (chOf W (trOf (s k).2.1)) =
    tLog W x (view h B outputs x w (chOf W (trOf (s k).2.1)) ((toMP W Pr eCm s).2 k))
        (trOf (s k).2.1, rootsOf (s k).2.1, eCm.symm (restOf (s k).2.1), (s k).2.2.2) ++
      W.comLog (eCm.symm (restOf (s k).2.1)) (rootsOf (s k).2.1)
        (view h B outputs x w (chOf W (trOf (s k).2.1)) ((toMP W Pr eCm s).2 k)) (chOf W (trOf (s k).2.1))
  rw [hcom w (s k).1 0 ((toMP W Pr eCm s).2 k) (rootsOf (s k).2.1) _ _,
    hcom w (s k).1 0 ((toMP W Pr eCm s).2 k) (rootsOf (s k).2.1) _ _]
  congr 1
  apply List.map_congr_left
  intro c0 hc0
  obtain ⟨hdep, hne⟩ := hidden (Pr.openFib (chOf W (trOf (s k).2.1))) c0
    ((hop.covers _ c0).mp hc0) c (fun ho => hnp (pub_of_opened W Pr hop _ c ho)) q hs
  refine Prod.ext ?_ ?_
  · show Pr.caddr _ _ _ _ _ _ _ _ _ = Pr.caddr _ _ _ _ _ _ _ _ _
    rw [hb, hb]
    convert gram_rest_update (W.pubBytes x) W.vtag
      (Pr.leafVal h w x ((toMP W Pr eCm s).2 k) (chOf W (trOf (s k).2.1))) (s k).1
      0 (restOf (s k).2.1) q u (cposOf c0) hdep
  · rcases c0 with i | q'
    · rfl
    · show Function.update (restOf (s k).2.1) q u q' = restOf (s k).2.1 q'
      exact Function.update_of_ne (fun e => hne (by rw [e])) _ _

theorem hit_cm (hb : RCommitBytes W Pr) (hop : ROpen Pr) (hcom : RComLog W Pr eCm h B outputs x)
    (k : Fin N) (c : CPos Pr.E₁ Pr.E₂) (i : Fin W.qmax) :
    HitFresh (fun s => chargedQ W Pr eCm N P h V w s (k, .inr c))
      (qryQ W Pr eCm N hN P h V B outputs x w adv i)
      (fun s => addrQ W Pr R N hN h B outputs x w s (k, .inr c)) (2 ^ 255) := by
  rcases hsrc : src c with i' | q
  · refine hitFresh_of_lens (Lens.fnAt k (secL W Pr i')) _ _ _
      (fun a => nzOf (fld (W.pubBytes x).length c a)) _ card_NZ ?_ ?_
      (fld_sec W Pr R N hN h B outputs x w hb k c i' hsrc)
    · intro s z hs
      exact (charged_tame W Pr eCm N P h V w _ (tame_sec W Pr i') k s z (k, .inr c)).mpr hs
    · intro s z _
      refine qry_tame W Pr eCm N hN P h V B outputs x w adv _ (tame_sec W Pr i') k s z (fun _ => ?_) i
      have e : (toMP W Pr eCm ((Lens.fnAt k (secL W Pr i')).set s z)).1 k = (toMP W Pr eCm s).1 k := by
        show (gM W Pr eCm (((Lens.fnAt k (secL W Pr i')).set s z) k)).1 = (gM W Pr eCm (s k)).1
        rw [Lens.fnAt_set_eq]
        rfl
      rw [e]
  · refine hitFresh_of_lens (Lens.fnAt k (vL W Pr (.inr (.inr (.inr q))))) _ _ _
      (fld (W.pubBytes x).length c) _ umin_le_card_ans ?_ ?_
      (fld_rest W Pr R N hN h B outputs x w hb k c q hsrc)
    · intro s u hs
      exact (charged_tame W Pr eCm N P h V w _ (tame_rest W Pr q) k s u (k, .inr c)).mpr hs
    · intro s u hs
      refine qry_tame W Pr eCm N hN P h V B outputs x w adv _ (tame_rest W Pr q) k s u (fun ha => ?_) i
      exact verLog_rest W Pr eCm N h B outputs x w hb hop hcom s k c q hsrc
        (fun hp => hs ⟨ha, hp⟩) u

end Hit

#print axioms qry_tame
#print axioms hit_tr
#print axioms verLog_rest
#print axioms hit_cm
end R1Z.EventsR1PBin
