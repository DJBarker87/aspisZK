import R1Z.QueryScanSharedHistoryMass
import R1Z.QueryScanRealFreshMass
import R1Z.QueryScanRealLazyJoin

/-! Conservative marginal min-entropy of the actual scan state. This is not
conditional entropy after revealing that state, nor is marginal min-entropy
alone used as a pair-collision hypothesis. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.QueryScanRealEntropy
open R0P R0Z R0Z.JointView R0Z.FsStatement R0Z.FsAbort R0Z.FsGood R0Z.HvzkV
  R0Z.FsAbortBounds R1Z.GamesR1 R1Z.GamesR1PBin R1Z.CouplingR1PBin
  R1Z.LensR1 R1Z.EventsR1PBin R1Z.PremisesR1PBin R1Z.TranscriptR1 R1Z.QueryScanFreshInputs R1Z.LayoutR1PBin
  R1Z.QueryScanRealLazyBound R1Z.QueryScanRealFreshMass
attribute [local instance] Classical.propDecidable

theorem lazy_budget_sharp {M : ℕ} (hM : M ≤ 2^25) :
    lazyBudget M ≤ 1 / (2 : ℚ)^204 := by
  apply (QueryScanRealLazyJoin.lazy_budget_mono hM).trans
  have hp : ((2^25 : ℕ) : ℚ) = (2 : ℚ)^25 := by norm_cast
  unfold lazyBudget
  rw [hp]
  have h25 : (2 : ℚ)^25 ≤ (2 : ℚ)^50 := pow_le_pow_right₀ (by norm_num) (by omega)
  have hh : (2 : ℚ)^25 * 2^25 = (2 : ℚ)^50 := by rw [← pow_add]
  rw [hh]
  calc _ ≤ (2 : ℚ)^50 / 2^255 + (2 : ℚ)^50 / 2^255 := by gcongr
       _ = 1 / (2 : ℚ)^204 := by
         rw [show (255 : ℕ) = 50 + 204 + 1 from rfl, pow_add, pow_add, pow_one]
         field_simp
         <;> ring

variable {K CommitHandle Aux : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K] {F : Subfield K}
variable (W : R1Wire K CommitHandle Aux) (Pr : R1ProverP K CommitHandle Aux F W)
  (R : RomModel W) (N : ℕ) (hN : 0 < N) (h : HonestProver K) (B : PackBasis F)
  (outputs : Statement K CommitHandle → Challenges K → Aux)
  (x : Statement K CommitHandle) (w : h.Instance)

def realState (k : Fin N) (j : Fin 8) (r : W.Tab × (Fin N → SecP)) : OracleAnswer :=
  attVec W Pr (realVector W Pr N h B outputs x w r) k (.inl (predecessor j))

/-- Coordinate projection factored over generic carriers to avoid concrete
byte Fintype instance normalization. -/
theorem coordinate_point {J U V S : Type} [Fintype J] [Fintype U] [Nonempty U]
    [Fintype V] [Nonempty V] [Fintype S] [Nonempty S]
    (k : J) (z : U) :
    eventMass (fun p : S × (J → U) × V => p.2.1 k = z) = 1 / Fintype.card U := by
  have h1 : MP (fun p : S × (J → U) × V => p.2) := mp_snd
  have h2 : MP (fun p : (J → U) × V => p.1) := mp_fst
  have hm := (mp_comp h1 h2) (fun q => if q k = z then (1 : ℚ) else 0)
  classical
  have he := QueryScanSharedHistoryMass.eval_point_mass k z
  exact hm.trans he

include hN in
theorem real_state_point (hin : RAddrIn W Pr R h B outputs x w)
    (hc : RCausal W Pr h B outputs x w) (hb : RCommitBytes W Pr)
    (hE₁ : Pr.E₁ ≤ 2^64) (hE₂ : Pr.E₂ ≤ 2^64)
    (k : Fin N) (j : Fin 8) (z : OracleAnswer) :
    eventMass (fun r => realState W Pr N h B outputs x w k j r = z) ≤
      lazyBudget (N * n1 W Pr) + 1 / (2 : ℚ)^256 := by
  have hm := meanR_P W Pr R h B outputs x w N hN hc
    (fun r => if realState W Pr N h B outputs x w k j r = z then (1 : ℚ) else 0)
  have hm' : eventMass (fun s : Fin N → AttS (F := F) W Pr =>
      realState W Pr N h B outputs x w k j (toRP W Pr R h B outputs x w hN s) = z) =
      eventMass (fun r => realState W Pr N h B outputs x w k j r = z) := by
    unfold eventMass
    convert hm using 1 <;> congr 1 <;> funext a <;> split_ifs <;> rfl
  rw [← hm']
  have hsub : ∀ s : Fin N → AttS (F := F) W Pr,
      realState W Pr N h B outputs x w k j (toRP W Pr R h B outputs x w hN s) = z →
      lazyBad W Pr R N hN h B outputs x w s ∨ (s k).2.1 (.inl (predecessor j)) = z := by
    intro s hs
    by_cases hn : lazyBad W Pr R N hN h B outputs x w s
    · exact Or.inl hn
    · right
      unfold realState at hs
      rw [real_vector_toRP W Pr R N hN h B outputs x w hin hc s hn, attVec_uVec] at hs
      exact hs
  apply (eventMass_mono _ _ hsub).trans
  have hp : eventMass (fun s : Fin N → AttS (F := F) W Pr =>
      (s k).2.1 (.inl (predecessor j)) = z) = 1 / (2 : ℚ)^256 := by
    have he := mean_eval k
      (fun a : AttS (F := F) W Pr => if a.2.1 (.inl (predecessor j)) = z then (1 : ℚ) else 0)
    have hc' := coordinate_point (S := SecP) (V := Tape K F × W.Tab)
      (.inl (predecessor j) : Pos1 Pr.E₁ Pr.E₂) z
    have hz : eventMass (fun a : AttS (F := F) W Pr =>
        a.2.1 (.inl (predecessor j)) = z) = 1 / (2 : ℚ)^256 := by
      trans 1 / (Fintype.card OracleAnswer : ℚ)
      · convert hc' using 1 <;> unfold eventMass <;> apply QueryScanIdealHistory.mean_fintype_transport
      · rw [QueryScanSharedHistoryMass.answer_cardinality, Nat.cast_pow, Nat.cast_ofNat]
    have he' : eventMass (fun s : Fin N → AttS (F := F) W Pr =>
        (s k).2.1 (.inl (predecessor j)) = z) =
        eventMass (fun a : AttS (F := F) W Pr => a.2.1 (.inl (predecessor j)) = z) := by
      unfold eventMass
      convert he using 1 <;> congr 1 <;> funext a <;> split_ifs <;> rfl
    exact he'.trans hz
  exact (eventMass_or_le _ _).trans (add_le_add
    (lazy_bad_mass W Pr R N hN h B outputs x w hb hE₁ hE₂) hp.le)

include hN in
/-- A deliberately conservative, proved 190-bit marginal min-entropy. The
fresh ideal predecessor coordinate has 256 bits; the loss pays all honest
collision histories in this coarse argument. -/
theorem real_state_min_entropy (hin : RAddrIn W Pr R h B outputs x w)
    (hc : RCausal W Pr h B outputs x w) (hb : RCommitBytes W Pr)
    (hE₁ : Pr.E₁ ≤ 2^64) (hE₂ : Pr.E₂ ≤ 2^64)
    (hM : N * n1 W Pr ≤ 2^25) (k : Fin N) (j : Fin 8) (z : OracleAnswer) :
    eventMass (fun r => realState W Pr N h B outputs x w k j r = z) ≤
      1 / (2 : ℚ)^190 := by
  apply (real_state_point W Pr R N hN h B outputs x w hin hc hb hE₁ hE₂ k j z).trans
  have hsmall := lazy_budget_sharp hM
  have h256 := QueryScanHistoryRealNumerics.dyadic_mono (by omega : 204 ≤ 256)
  calc _ ≤ 1 / (2 : ℚ)^204 + 1 / (2 : ℚ)^204 := add_le_add hsmall h256
       _ = 1 / (2 : ℚ)^203 := by
         rw [show (204 : ℕ) = 203 + 1 from rfl, pow_add, pow_one]
         field_simp
         <;> ring
       _ ≤ 1 / (2 : ℚ)^190 := QueryScanHistoryRealNumerics.dyadic_mono (by omega)

#print axioms lazy_budget_sharp
#print axioms coordinate_point
#print axioms real_state_point
#print axioms real_state_min_entropy
end R1Z.QueryScanRealEntropy
