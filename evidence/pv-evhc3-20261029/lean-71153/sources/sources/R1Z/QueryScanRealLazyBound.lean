import R1Z.QueryScanFreshInputs

/-! A conservative real-model law from the retained lazy coupling. This
charges a single *honest program* collision event; it does not include any
adversary rereads. No claim of the sharper scan-only entropy law is made. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.QueryScanRealLazyBound
open R0P R0Z R0Z.JointView R0Z.FsStatement R0Z.FsAbort R0Z.FsAbortBounds
  R0Z.HvzkV R1Z.GamesR1 R1Z.GamesR1PBin R1Z.LensR1 R1Z.TranscriptR1
  R1Z.LazyFrozen R1Z.CouplingR1PBin R1Z.AgreeR1PBin R1Z.EventsR1PBin R1Z.FinalR1PBin
  R1Z.LayoutR1PBin R1Z.QueryScanPrivacyFinal
attribute [local instance] Classical.propDecidable

variable {K CommitHandle Aux : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K] {F : Subfield K}
variable (W : R1Wire K CommitHandle Aux) (Pr : R1ProverP K CommitHandle Aux F W)
  (R : RomModel W) (N : ℕ) (hN : 0 < N) (h : HonestProver K) (B : PackBasis F)
  (outputs : Statement K CommitHandle → Challenges K → Aux)
  (x : Statement K CommitHandle) (w : h.Instance)

/-- Fixed all-honest-read event on the independent lazy coupling space. -/
def lazyBad (s : Fin N → AttS (F := F) W Pr) : Prop :=
  CollEv (N * n1 W Pr) (fun _ => True)
    (fun g s => addrQ W Pr R N hN h B outputs x w s (posE W Pr N g)) s ∨
  ∃ g, addrQ W Pr R N hN h B outputs x w s (posE W Pr N g) = W.pubBytes x

def lazyBudget (M : ℕ) : ℚ := (M : ℚ) * M / 2^255 + (M : ℚ) / 2^255

theorem lazy_bad_mass (hb : RCommitBytes W Pr)
    (hE₁ : Pr.E₁ ≤ 2^64) (hE₂ : Pr.E₂ ≤ 2^64) :
    mass (lazyBad W Pr R N hN h B outputs x w) ≤ lazyBudget (N * n1 W Pr) := by
  apply (mass_or_le _ _).trans
  apply add_le_add
  · exact collEv_mass_fresh _ _ (by positivity) _ _
      (fun i j hij _ => pair_all W Pr R N hN h B outputs x w hb hE₁ hE₂
        _ _ (fun he => ne_of_lt hij ((posE W Pr N).injective he)))
  · have hp := mass_exists_le_card
      (fun g s => addrQ W Pr R N hN h B outputs x w s (posE W Pr N g) = W.pubBytes x)
      (1 / ((2^255 : ℕ) : ℚ)) (fun g =>
        pairFresh_mass _ _ _ (by positivity)
          (Or.inr (pf_pub W Pr R N hN h B outputs x hb w (posE W Pr N g))))
    simpa only [Fintype.card_fin, Nat.cast_pow, Nat.cast_ofNat, mul_one_div] using hp

theorem off_lazy_bad_run (hin : RAddrIn W Pr R h B outputs x w)
    (hc : RCausal W Pr h B outputs x w)
    (s : Fin N → AttS (F := F) W Pr)
    (hn : ¬ lazyBad W Pr R N hN h B outputs x w s) :
    runC (gAddr W Pr h B outputs x w (fun k => (s k).1) (dS W Pr R N hN x s))
      (lookA R (TP W Pr R N hN h B outputs x w s)) 0 = uVec W Pr s := by
  apply run_eq_lazy W Pr R N hN h B outputs x w hin hc s
  · intro g j hj he
    exact hn (Or.inl ⟨j, g, hj, Or.inl trivial, he⟩)
  · intro g he
    exact hn (Or.inr ⟨g, he⟩)

/-- Actual vector evaluated by the honest real experiment, before publication. -/
def realVector (r : W.Tab × (Fin N → SecP)) : Fin (N * n1 W Pr) → OracleAnswer :=
  runC (gAddr W Pr h B outputs x w r.2 (W.look r.1 (W.pubBytes x))) (W.look r.1) 0

theorem real_vector_toRP (hin : RAddrIn W Pr R h B outputs x w)
    (hc : RCausal W Pr h B outputs x w)
    (s : Fin N → AttS (F := F) W Pr)
    (hn : ¬ lazyBad W Pr R N hN h B outputs x w s) :
    realVector W Pr N h B outputs x w (toRP W Pr R h B outputs x w hN s) =
      uVec W Pr s := by
  unfold realVector
  simp only [look_toRP, TP_pub]
  change runC (gAddr W Pr h B outputs x w (fun k => (s k).1) (dS W Pr R N hN x s))
    (W.look (toRP W Pr R h B outputs x w hN s).1) 0 = _
  rw [show W.look (toRP W Pr R h B outputs x w hN s).1 =
    lookA R (TP W Pr R N hN h B outputs x w s) from funext (look_toRP W Pr R N hN h B outputs x w s)]
  exact off_lazy_bad_run W Pr R N hN h B outputs x w hin hc s hn

/-- Fixed parser failure at its own selected first-stop block. -/
def parserBad (q : Fin 8 → OracleAnswer) : Prop :=
  ∃ count, AspisV8R19.Q22WordScan.finish
    (PhaseSamplerParserBin.scanned (PhaseQueryScanBin.stop PhaseSamplerParserBin.done q) q).1 =
      .error count

def realBad (k : Fin N) (r : W.Tab × (Fin N → SecP)) : Prop :=
  parserBad (fun j => attVec W Pr (realVector W Pr N h B outputs x w r) k (.inl (.qb j)))

def lazyScanBad (k : Fin N) (s : Fin N → AttS (F := F) W Pr) : Prop :=
  parserBad (fun j => (s k).2.1 (.inl (.qb j)))

theorem parser_bad_mass : eventMass parserBad ≤ scanProbability := by
  have hi : ∀ q, parserBad q → AspisR1.QueryScanModelFailure.fails
      (QueryScanIndependentHistory.words64 q) := by
    intro q hq
    obtain ⟨count, hcount⟩ := hq
    exact QueryScanFirstStopHistory.selected_failure_implies_words_failure _ count hcount
  exact (eventMass_mono _ _ hi).trans (by
    simpa only [true_and] using
      QueryScanIndependentHistory.reached_failure_le (fun _ => True))

theorem lazy_scan_bad_mass (k : Fin N) :
    eventMass (lazyScanBad W Pr N k) ≤ scanProbability := by
  have h1 : MP (fun a : AttS (F := F) W Pr => a.2) := mp_snd
  have h2 : MP (fun a : (Pos1 Pr.E₁ Pr.E₂ → OracleAnswer) × (Tape K F × W.Tab) => a.1) := mp_fst
  have h3 := QueryScanIdealHistory.coordinates_uniform (U := OracleAnswer)
    (fun j : Fin 8 => (Sum.inl (.qb j) : Pos1 Pr.E₁ Pr.E₂))
    (by intro a b he; cases he; rfl)
  have hh1 := (mp_comp h1 h2)
    (fun v => if parserBad (fun j => v (.inl (.qb j))) then (1 : ℚ) else 0)
  have hh3 := h3 (fun q => if parserBad q then (1 : ℚ) else 0)
  have hh : mean (fun a : AttS (F := F) W Pr =>
      if parserBad (fun j => a.2.1 (.inl (.qb j))) then (1 : ℚ) else 0) =
      eventMass parserBad := by
    trans mean (fun v : Pos1 Pr.E₁ Pr.E₂ → OracleAnswer =>
      if parserBad (fun j => v (.inl (.qb j))) then (1 : ℚ) else 0)
    · exact hh1
    · convert hh3 using 1 <;> apply QueryScanIdealHistory.mean_fintype_transport
  have hm := mean_eval k
    (fun a : AttS (F := F) W Pr => if parserBad (fun j => a.2.1 (.inl (.qb j))) then (1 : ℚ) else 0)
  exact hm.le.trans (hh.le.trans parser_bad_mass)

include hN in
/-- A single global lazy collision budget, rather than one copy per attempt. -/
theorem real_bad_union_mass (hin : RAddrIn W Pr R h B outputs x w)
    (hc : RCausal W Pr h B outputs x w) (hb : RCommitBytes W Pr)
    (hE₁ : Pr.E₁ ≤ 2^64) (hE₂ : Pr.E₂ ≤ 2^64) :
    eventMass (fun r => ∃ k, realBad W Pr N h B outputs x w k r) ≤
      lazyBudget (N * n1 W Pr) + (N : ℚ) * scanProbability := by
  have hm := meanR_P W Pr R h B outputs x w N hN hc
    (fun r => if ∃ k, realBad W Pr N h B outputs x w k r then (1 : ℚ) else 0)
  have hm' : eventMass (fun s : Fin N → AttS (F := F) W Pr =>
      ∃ k, realBad W Pr N h B outputs x w k (toRP W Pr R h B outputs x w hN s)) =
      eventMass (fun r => ∃ k, realBad W Pr N h B outputs x w k r) := by
    unfold eventMass
    convert hm using 1 <;> congr 1 <;> funext z <;> split_ifs <;> rfl
  rw [← hm']
  change mass (fun s : Fin N → AttS (F := F) W Pr =>
    ∃ k, realBad W Pr N h B outputs x w k (toRP W Pr R h B outputs x w hN s)) ≤ _
  have hsub : ∀ s : Fin N → AttS (F := F) W Pr,
      (∃ k, realBad W Pr N h B outputs x w k (toRP W Pr R h B outputs x w hN s)) →
      lazyBad W Pr R N hN h B outputs x w s ∨ ∃ k, lazyScanBad W Pr N k s := by
    intro s hs
    by_cases hn : lazyBad W Pr R N hN h B outputs x w s
    · exact Or.inl hn
    · right
      obtain ⟨k, hk⟩ := hs
      refine ⟨k, ?_⟩
      unfold realBad at hk
      rw [real_vector_toRP W Pr R N hN h B outputs x w hin hc s hn, attVec_uVec] at hk
      exact hk
  exact (mass_mono _ _ hsub).trans ((mass_or_le _ _).trans (add_le_add
      (lazy_bad_mass W Pr R N hN h B outputs x w hb hE₁ hE₂)
      (by simpa only [Fintype.card_fin] using (mass_exists_le_card
        (lazyScanBad W Pr N) scanProbability (fun k => lazy_scan_bad_mass W Pr N k)))))

#print axioms real_vector_toRP
#print axioms parser_bad_mass
#print axioms lazy_scan_bad_mass
#print axioms real_bad_union_mass
#print axioms lazy_bad_mass
#print axioms off_lazy_bad_run
end R1Z.QueryScanRealLazyBound
