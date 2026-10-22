import R1Z.ProverCommitNormalCarrier42

/-! Charged adaptive observer hits after the conditional public normalization.
Existing private-field bounds are retained; public bindings are excluded. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverCommitCharged42
open R0P R0Z R0Z.JointView R0Z.FsStatement R0Z.FsAbort R0Z.FsAbortBounds R0Z.HvzkV
open GamesR1 GamesR1PBin CouplingR1PBin EventsR1PBin LayoutR1PBin LensR1
open ProverCommitNormalCarrier42
attribute [local instance] Classical.propDecidable
variable {K CommitHandle Aux : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K] {F : Subfield K}
variable (W : R1Wire K CommitHandle Aux) (Pr : R1ProverP K CommitHandle Aux F W) (R : RomModel W)
  (eCm : W.Cm ≃ (RIdx → OracleAnswer)) (N : Nat) (hN : 0<N) (P : Challenges K → Prop)
  (h : HonestProver K) (V : Challenges K → h.Instance → Prop) (B : PackBasis F)
  (outputs : Statement K CommitHandle → Challenges K → Aux) (x : Statement K CommitHandle)
  (w : h.Instance) (adv : R1Adv K CommitHandle Aux)

theorem hit_private (hb : RCommitBytes W Pr) (hop : ROpen Pr) (hcom : RComLog W Pr eCm h B outputs x)
    (nonce : Fin N → NZ) (answers : Fin N → Fin 2 → OracleAnswer)
    (k : Fin N) (c : CPos Pr.E₁ Pr.E₂) (hc : ProverCommitPrivateBounds42.privatePos W Pr c)
    (i : Fin W.qmax) :
    HitFresh (fun s => chargedQ W Pr eCm N P h V w (normalize W Pr nonce answers s) (k,.inr c))
      (fun s => qryQ W Pr eCm N hN P h V B outputs x w adv i (normalize W Pr nonce answers s))
      (fun s => addrQ W Pr R N hN h B outputs x w (normalize W Pr nonce answers s) (k,.inr c)) (2^255) := by
  have privateSource := ProverCommitPrivateBounds42.src_private W Pr c hc
  cases source : src c with
  | inl j =>
    have nj := privateSource.1 j source
    have commute := normalize_lens W Pr nonce answers (secL W Pr j)
      (fun nonce first second a z => block_sec W Pr nonce first second j nj a z) k
    refine hitFresh_of_lens (Lens.fnAt k (secL W Pr j)) _ _ _
      (fun a => nzOf (fld (W.pubBytes x).length c a)) _ card_NZ ?_ ?_ ?_
    · intro s z hs
      rw [commute]
      exact (charged_tame W Pr eCm N P h V w _ (tame_sec W Pr j) k _ z (k,.inr c)).mpr hs
    · intro s z hs
      rw [commute]
      refine qry_tame W Pr eCm N hN P h V B outputs x w adv _ (tame_sec W Pr j) k _ z (fun _ => ?_) i
      have eq : (toMP W Pr eCm ((Lens.fnAt k (secL W Pr j)).set
          (normalize W Pr nonce answers s) z)).1 k =
          (toMP W Pr eCm (normalize W Pr nonce answers s)).1 k := by
        change (gM W Pr eCm (((Lens.fnAt k (secL W Pr j)).set _ z) k)).1 = _
        rw [Lens.fnAt_set_eq]
        rfl
      rw [eq]
    · intro s z
      rw [commute]
      exact fld_sec W Pr R N hN h B outputs x w hb k c j source _ z
  | inr q =>
    have nq := privateSource.2 q source
    have commute := normalize_lens W Pr nonce answers (vL W Pr (.inr (.inr (.inr q))))
      (fun nonce first second a u => block_rest W Pr nonce first second q nq a u) k
    refine hitFresh_of_lens (Lens.fnAt k (vL W Pr (.inr (.inr (.inr q))))) _ _ _
      (fld (W.pubBytes x).length c) _ umin_le_card_ans ?_ ?_ ?_
    · intro s u hs
      rw [commute]
      exact (charged_tame W Pr eCm N P h V w _ (tame_rest W Pr q) k _ u (k,.inr c)).mpr hs
    · intro s u hs
      rw [commute]
      refine qry_tame W Pr eCm N hN P h V B outputs x w adv _ (tame_rest W Pr q) k _ u (fun ha => ?_) i
      exact verLog_rest W Pr eCm N h B outputs x w hb hop hcom _ k c q source
        (fun hp => hs ⟨ha,hp⟩) u
    · intro s u
      rw [commute]
      exact fld_rest W Pr R N hN h B outputs x w hb k c q source _ u

#print axioms hit_private
end R1Z.ProverCommitCharged42
