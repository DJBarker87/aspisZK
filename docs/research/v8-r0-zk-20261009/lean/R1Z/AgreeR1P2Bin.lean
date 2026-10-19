import R1Z.AgreeR1PBin

-- Binary-format copy of `R1Z.AgreeR1P2` (LOG D76): the text is unchanged except that it is
-- built over `GamesR1PBin` / `LayoutR1P*Bin` (binary node index and `0x12 ‖ 2 children`).

/-! Agreement of the real and middle games, part 2 (DESIGN-R1-REAL §5):
`agreeP` — outside the hit event, collisions, exhaustion and digest hits,
the real game on `toRP s` and the middle game of `abR1` on `toMP s` publish
the same ROM view, so their tests agree.  Premises: `RAddrIn`, `RCausal`,
`RComLog`, and `Vp h = V` (the real game accepts on the same no-pole
predicate as the middle game). -/
set_option autoImplicit false
noncomputable section
namespace R1Z.AgreeR1PBin
open R0P R0Z R0Z.JointView R0Z.FsStatement R0Z.FsAbort R0Z.FsAbortBounds R0Z.HvzkV
  R1Z.Batched R1Z.LensR1 R1Z.TranscriptR1 R1Z.GamesR1 R1Z.LazyFrozen R1Z.GamesR1PBin
  R1Z.CouplingR1PBin R1Z.LayoutR1PBin R1Z.EventsR1PBin
attribute [local instance] Classical.propDecidable

theorem lookup_none' {ι α β : Type} [BEq α] [LawfulBEq α] (G : ι → α × β) (y : α) :
    ∀ l : List ι, (∀ i ∈ l, (G i).1 ≠ y) → List.lookup y (l.map G) = none
  | [], _ => rfl
  | i :: l, h => by
      rw [List.map_cons]
      rcases hG : G i with ⟨a, b⟩
      rw [List.lookup_cons]
      have hb : (y == a) = false := by
        rw [beq_eq_false_iff_ne]
        intro e
        apply h i List.mem_cons_self
        rw [hG, ← e]
      rw [hb]
      exact lookup_none' G y l (fun j hj => h j (List.mem_cons_of_mem _ hj))

theorem lookup_some' {ι α β : Type} [BEq α] [LawfulBEq α] (G : ι → α × β) (y : α) (b : β) :
    ∀ l : List ι, (∃ i ∈ l, (G i).1 = y) → (∀ i ∈ l, (G i).1 = y → (G i).2 = b) →
      List.lookup y (l.map G) = some b
  | [], ⟨_, hi, _⟩, _ => absurd hi List.not_mem_nil
  | i :: l, ⟨i₀, hi₀, he⟩, h => by
      rw [List.map_cons]
      rcases hG : G i with ⟨a, v⟩
      rw [List.lookup_cons]
      by_cases hyi : a = y
      · have hb : (y == a) = true := by rw [beq_iff_eq]; exact hyi.symm
        rw [hb]
        have hv : v = b := by
          have := h i List.mem_cons_self (by rw [hG]; exact hyi)
          rw [hG] at this
          exact this
        exact congrArg some hv
      · have hb : (y == a) = false := by rw [beq_eq_false_iff_ne]; exact fun e => hyi e.symm
        rw [hb]
        rcases List.mem_cons.mp hi₀ with rfl | hl
        · rw [hG] at he
          exact absurd he hyi
        · exact lookup_some' G y b l ⟨i₀, hl, he⟩ (fun j hj => h j (List.mem_cons_of_mem _ hj))

variable {K CommitHandle Aux : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K] {F : Subfield K}

section Agree
variable (W : R1Wire K CommitHandle Aux) (Pr : R1ProverP K CommitHandle Aux F W) (R : RomModel W)
  (eCm : W.Cm ≃ (RIdx → OracleAnswer)) (N : ℕ) (hN : 0 < N) (P : Challenges K → Prop)
  (Vp : (h : HonestProver K) → Challenges K → h.Instance → Prop)
  (h : HonestProver K) (V : Challenges K → h.Instance → Prop) (B : PackBasis F)
  (outputs : Statement K CommitHandle → Challenges K → Aux) (x : Statement K CommitHandle)
  (w : h.Instance) (adv : R1Adv K CommitHandle Aux)

/-- The published positions of attempt `k`, in the verifier's order. -/
def Lpos (s : Fin N → AttS (F := F) W Pr) (k : Fin N) : List (Pos1 Pr.E₁ Pr.E₂) :=
  schedule.map Sum.inl ++ (Pr.openList (chOf W (trOf (s k).2.1))).map (fun c => Sum.inr (cposOf c))

def fL (s : Fin N → AttS (F := F) W Pr) (k : Fin N) (p : Pos1 Pr.E₁ Pr.E₂) : List UInt8 × OracleAnswer :=
  (addrQ W Pr R N hN h B outputs x w s (k, p), (s k).2.1 p)

theorem fail_eqP (adv : R1Adv K CommitHandle Aux) (x : Statement K CommitHandle)
    (c : Fin N → R1Coins W.Cm W.Tab) :
    (abR1 W N hN).fail adv x c = ⟨W.failView, runLog (adv.prog W.failView []) (W.look (c ⟨0, hN⟩).2.2.2) W.qmax⟩ :=
  rfl

theorem extend_eqP (adv : R1Adv K CommitHandle Aux) (x : Statement K CommitHandle)
    (c : Fin N → R1Coins W.Cm W.Tab) (k : Fin N) (v : View K CommitHandle Aux R1Bat) :
    (abR1 W N hN).extend adv x c k v = ⟨v, verLog W x v (c k) ++
      runLog (adv.prog v (verLog W x v (c k))) (progOracle W x v (c k) (c ⟨0, hN⟩).2.2.2) W.qmax⟩ :=
  rfl

theorem mem_runLog_idx (p : OProg) (O : List UInt8 → OracleAnswer) (n : ℕ)
    (e : List UInt8 × OracleAnswer) (he : e ∈ runLog p O n) :
    ∃ i : Fin n, (runLog p O n).getD i.val ([], fun _ => 0) = e :=
  mem_getD _ _ n (length_runLog n p O) e he

theorem real_eqP (r : W.Tab × (Fin N → SecP)) :
    realTest h B outputs (fsR1P W Pr N hN P Vp) adv x w r =
      bit (adv.decide (realGameP W Pr N P Vp h B outputs adv x w r)) := rfl

theorem middle_eqP (ct : (Fin N → R1Coins W.Cm W.Tab) × (Fin N → Tape K F)) :
    middleRealAbortV P h V B outputs (fsR1P W Pr N hN P Vp) (abR1P W N hN) adv x w ct =
      bit (adv.decide (match accR W N P h V w ct with
        | none => (abR1 W N hN).fail adv x ct.1
        | some k => (abR1 W N hN).extend adv x ct.1 k
            (view h B outputs x w (drawW W (ct.1 k)) (ct.2 k)))) := by
  unfold middleRealAbortV retryTest
  split
  · next heq =>
      rw [show accR W N P h V w ct = none from heq]
      rfl
  · next k heq =>
      rw [show accR W N P h V w ct = some k from heq]
      rfl

theorem tape_eq (s : Fin N → AttS (F := F) W Pr) (k : Fin N)
    (hk : Pr.tapeOf (e₁Of (s k).2.1) (e₂Of (s k).2.1) ≠ none) :
    tapeR W Pr (s k).2.1 = (toMP W Pr eCm s).2 k := by
  obtain ⟨τ, hτ⟩ := Option.ne_none_iff_exists'.mp hk
  show (Pr.tapeOf (e₁Of (s k).2.1) (e₂Of (s k).2.1)).getD tape0 =
    (Pr.tapeOf (e₁Of (s k).2.1) (e₂Of (s k).2.1)).getD (s k).2.2.1
  rw [hτ]
  rfl

theorem attOut_log (hin : RAddrIn W Pr R h B outputs x w) (hc : RCausal W Pr h B outputs x w)
    (s : Fin N → AttS (F := F) W Pr)
    (hrun : runC (gAddr W Pr h B outputs x w (fun k => (s k).1) (dS W Pr R N hN x s))
      (lookA R (TP W Pr R N hN h B outputs x w s)) 0 = uVec W Pr s) (k : Fin N) :
    (attOut W Pr h B outputs x w (lookA R (TP W Pr R N hN h B outputs x w s)) (s k).1
      (dS W Pr R N hN x s) (s k).2.1).log =
      (Lpos W Pr N s k).map (fL W Pr R N hN h B outputs x w s k) := by
  unfold Lpos
  rw [List.map_append, List.map_map, List.map_map]
  show List.map _ schedule ++ List.map _ _ = _
  congr 1
  · apply List.map_congr_left
    intro j _
    refine Prod.ext rfl ?_
    exact ans_eq W Pr R N hN h B outputs x w hin hc s hrun k (.inl j)
  · apply List.map_congr_left
    intro c _
    refine Prod.ext rfl ?_
    exact ans_eq W Pr R N hN h B outputs x w hin hc s hrun k (.inr (cposOf c))

theorem verLog_eq (hcom : RComLog W Pr eCm h B outputs x) (s : Fin N → AttS (F := F) W Pr) (k : Fin N)
    (hk : Pr.tapeOf (e₁Of (s k).2.1) (e₂Of (s k).2.1) ≠ none) :
    verLog W x (view h B outputs x w (drawW W ((toMP W Pr eCm s).1 k)) ((toMP W Pr eCm s).2 k))
        ((toMP W Pr eCm s).1 k) =
      (Lpos W Pr N s k).map (fL W Pr R N hN h B outputs x w s k) := by
  have ht := tape_eq W Pr eCm N s k hk
  have e : (toMP W Pr eCm s).1 k = (trOf (s k).2.1, rootsOf (s k).2.1, eCm.symm (restOf (s k).2.1),
      (s k).2.2.2) := rfl
  rw [e]
  unfold verLog drawW
  dsimp only
  rw [hcom w (s k).1 (dS W Pr R N hN x s) ((toMP W Pr eCm s).2 k) (rootsOf (s k).2.1)
    (restOf (s k).2.1) (chOf W (trOf (s k).2.1))]
  unfold tLog Lpos
  dsimp only
  rw [List.map_append, List.map_map, List.map_map]
  refine congrArg₂ (· ++ ·) ?_ ?_
  · apply List.map_congr_left
    intro j _
    refine Prod.ext ?_ rfl
    show addr j (recP W x (view h B outputs x w (chOf W (trOf (s k).2.1)) ((toMP W Pr eCm s).2 k))
      (trOf (s k).2.1) (rootsOf (s k).2.1)) =
      addr j (recP W x (view h B outputs x w (chOf W (trOf (s k).2.1)) (tapeR W Pr (s k).2.1))
      (trOf (s k).2.1) (rootsOf (s k).2.1))
    rw [ht]
  · apply List.map_congr_left
    intro c _
    refine Prod.ext ?_ ?_
    · show Pr.caddr h w x (s k).1 (dS W Pr R N hN x s) ((toMP W Pr eCm s).2 k) (restOf (s k).2.1)
          (chOf W (trOf (s k).2.1)) (cposOf c) =
        Pr.caddr h w x (s k).1 (dS W Pr R N hN x s) (tapeR W Pr (s k).2.1) (restOf (s k).2.1)
          (chOf W (trOf (s k).2.1)) (cposOf c)
      rw [ht]
    · rcases c with i | q <;> rfl

/-- The real game's per-attempt outputs on the coupling. -/
theorem realOut_eq (hin : RAddrIn W Pr R h B outputs x w) (hc : RCausal W Pr h B outputs x w)
    (s : Fin N → AttS (F := F) W Pr)
    (hrun : runC (gAddr W Pr h B outputs x w (fun k => (s k).1) (dS W Pr R N hN x s))
      (lookA R (TP W Pr R N hN h B outputs x w s)) 0 = uVec W Pr s) (k : Fin N) :
    realOut W Pr h B outputs x w (W.look (toRP W Pr R h B outputs x w hN s).1)
        (toRP W Pr R h B outputs x w hN s).2 k =
      attOut W Pr h B outputs x w (lookA R (TP W Pr R N hN h B outputs x w s)) (s k).1
        (dS W Pr R N hN x s) (s k).2.1 := by
  have hH : W.look (toRP W Pr R h B outputs x w hN s).1 = lookA R (TP W Pr R N hN h B outputs x w s) :=
    funext (look_toRP W Pr R N hN h B outputs x w s)
  unfold realOut
  rw [hH, TP_pub, show (toRP W Pr R h B outputs x w hN s).2 = fun k => (s k).1 from rfl, hrun,
    attVec_uVec]

/-- The middle oracle agrees with the real oracle on every middle read that is
not a charged prover read. -/
theorem oracle_acc (hin : RAddrIn W Pr R h B outputs x w) (hc : RCausal W Pr h B outputs x w)
    (hcom : RComLog W Pr eCm h B outputs x) (s : Fin N → AttS (F := F) W Pr)
    (hrun : runC (gAddr W Pr h B outputs x w (fun k => (s k).1) (dS W Pr R N hN x s))
      (lookA R (TP W Pr R N hN h B outputs x w s)) 0 = uVec W Pr s)
    (hcoll : ∀ p p' : Fin N × Pos1 Pr.E₁ Pr.E₂, p ≠ p' →
      addrQ W Pr R N hN h B outputs x w s p ≠ addrQ W Pr R N hN h B outputs x w s p')
    (k₀ : Fin N) (hacc : accM W Pr eCm N P h V w s = some k₀)
    (hk : Pr.tapeOf (e₁Of (s k₀).2.1) (e₂Of (s k₀).2.1) ≠ none)
    (y : List UInt8)
    (hy : ∀ p, addrQ W Pr R N hN h B outputs x w s p = y → ¬ chargedQ W Pr eCm N P h V w s p) :
    lookA R (TP W Pr R N hN h B outputs x w s) y =
      progOracle W x (view h B outputs x w (drawW W ((toMP W Pr eCm s).1 k₀)) ((toMP W Pr eCm s).2 k₀))
        ((toMP W Pr eCm s).1 k₀) ((toMP W Pr eCm s).1 ⟨0, hN⟩).2.2.2 y := by
  unfold progOracle
  rw [verLog_eq W Pr R eCm N hN h B outputs x w hcom s k₀ hk]
  by_cases hex : ∃ p, addrQ W Pr R N hN h B outputs x w s p = y
  · obtain ⟨⟨k, pp⟩, hp⟩ := hex
    have hnc := hy _ hp
    have hkk : k = k₀ ∧ pp ∈ Lpos W Pr N s k₀ := by
      rcases pp with j | c
      · have h1 : accM W Pr eCm N P h V w s = some k := by
          by_contra hne
          exact hnc hne
        rw [hacc] at h1
        have e := (Option.some.inj h1).symm
        subst e
        exact ⟨rfl, List.mem_append_left _ (List.mem_map.mpr ⟨j, mem_schedule j, rfl⟩)⟩
      · have h1 : accM W Pr eCm N P h V w s = some k ∧ pubC W Pr N s k c := by
          by_contra hne
          exact hnc hne
        rw [hacc] at h1
        have e := (Option.some.inj h1.1).symm
        subst e
        obtain ⟨c0, hc0, hcc⟩ := List.mem_map.mp h1.2
        exact ⟨rfl, List.mem_append_right _ (List.mem_map.mpr ⟨c0, hc0, by rw [hcc]⟩)⟩
    obtain ⟨rfl, hmem⟩ := hkk
    rw [lookup_some' (fL W Pr R N hN h B outputs x w s k) y
      ((s k).2.1 pp) (Lpos W Pr N s k) ⟨pp, hmem, hp⟩ (fun p' _ hp' => by
        by_cases e : p' = pp
        · subst e
          rfl
        · exact absurd (hp'.trans hp.symm) (hcoll (k, p') (k, pp) (fun ee => e (Prod.mk.inj ee).2)))]
    rw [← hp]
    exact ans_eq W Pr R N hN h B outputs x w hin hc s hrun k pp
  · push Not at hex
    rw [lookup_none' (fL W Pr R N hN h B outputs x w s k₀) y
      (Lpos W Pr N s k₀) (fun p _ => hex (k₀, p))]
    rw [lookA_off W Pr R N hN h B outputs x w hin s y (fun g => hex _), look_eqA]
    rfl

theorem oracle_none (hin : RAddrIn W Pr R h B outputs x w) (s : Fin N → AttS (F := F) W Pr)
    (hacc : accM W Pr eCm N P h V w s = none) (y : List UInt8)
    (hy : ∀ p, addrQ W Pr R N hN h B outputs x w s p = y → ¬ chargedQ W Pr eCm N P h V w s p) :
    lookA R (TP W Pr R N hN h B outputs x w s) y = W.look ((toMP W Pr eCm s).1 ⟨0, hN⟩).2.2.2 y := by
  have hex : ∀ p, addrQ W Pr R N hN h B outputs x w s p ≠ y := by
    intro p hp
    apply hy p hp
    rcases p with ⟨k, j | c⟩
    · show accM W Pr eCm N P h V w s ≠ some k
      rw [hacc]
      simp
    · show ¬ (accM W Pr eCm N P h V w s = some k ∧ _)
      rw [hacc]
      simp
  rw [lookA_off W Pr R N hN h B outputs x w hin s y (fun g => hex _), look_eqA]
  rfl

theorem firstGood_eq (hV : ∀ ch, Vp h ch w ↔ V ch w) (hin : RAddrIn W Pr R h B outputs x w)
    (hc : RCausal W Pr h B outputs x w) (s : Fin N → AttS (F := F) W Pr)
    (hrun : runC (gAddr W Pr h B outputs x w (fun k => (s k).1) (dS W Pr R N hN x s))
      (lookA R (TP W Pr R N hN h B outputs x w s)) 0 = uVec W Pr s)
    (hexh : ∀ k, Pr.tapeOf (e₁Of (s k).2.1) (e₂Of (s k).2.1) ≠ none) :
    firstGood (fun o : AttemptOut K CommitHandle Aux => P o.ch ∧ Vp h o.ch w ∧ o.exh = false)
        (realOut W Pr h B outputs x w (W.look (toRP W Pr R h B outputs x w hN s).1)
          (toRP W Pr R h B outputs x w hN s).2) =
      accR W N P h V w (toMP W Pr eCm s) := by
  have e1 : firstGood (fun o : AttemptOut K CommitHandle Aux => P o.ch ∧ Vp h o.ch w ∧ o.exh = false)
      (realOut W Pr h B outputs x w (W.look (toRP W Pr R h B outputs x w hN s).1)
        (toRP W Pr R h B outputs x w hN s).2) =
      firstGood (fun k => P (realOut W Pr h B outputs x w (W.look (toRP W Pr R h B outputs x w hN s).1)
          (toRP W Pr R h B outputs x w hN s).2 k).ch ∧
        Vp h (realOut W Pr h B outputs x w (W.look (toRP W Pr R h B outputs x w hN s).1)
          (toRP W Pr R h B outputs x w hN s).2 k).ch w ∧
        (realOut W Pr h B outputs x w (W.look (toRP W Pr R h B outputs x w hN s).1)
          (toRP W Pr R h B outputs x w hN s).2 k).exh = false) id := rfl
  have e2 : accR W N P h V w (toMP W Pr eCm s) =
      firstGood (fun k => P (chOf W (trOf (s k).2.1)) ∧ V (chOf W (trOf (s k).2.1)) w) id := rfl
  rw [e1, e2]
  apply firstGood_congr
  intro k
  simp only [id, realOut_eq W Pr R N hN h B outputs x w hin hc s hrun k]
  show P (chOf W (trOf (s k).2.1)) ∧ Vp h (chOf W (trOf (s k).2.1)) w ∧
      (Pr.tapeOf (e₁Of (s k).2.1) (e₂Of (s k).2.1)).isNone = false ↔ _
  have hn : (Pr.tapeOf (e₁Of (s k).2.1) (e₂Of (s k).2.1)).isNone = false := by
    cases ht : Pr.tapeOf (e₁Of (s k).2.1) (e₂Of (s k).2.1)
    · exact absurd ht (hexh k)
    · rfl
  rw [hn, hV]
  simp

/-- Agreement outside the events. -/
theorem agreeP (hin : RAddrIn W Pr R h B outputs x w) (hc : RCausal W Pr h B outputs x w)
    (hcom : RComLog W Pr eCm h B outputs x) (hV : ∀ ch, Vp h ch w ↔ V ch w)
    (s : Fin N → AttS (F := F) W Pr)
    (hhit : ∀ (p : Fin N × Pos1 Pr.E₁ Pr.E₂) (i : Fin W.qmax), chargedQ W Pr eCm N P h V w s p →
      qryQ W Pr eCm N hN P h V B outputs x w adv i s ≠ addrQ W Pr R N hN h B outputs x w s p)
    (hcoll : ∀ p p' : Fin N × Pos1 Pr.E₁ Pr.E₂, p ≠ p' →
      addrQ W Pr R N hN h B outputs x w s p ≠ addrQ W Pr R N hN h B outputs x w s p')
    (hexh : ∀ k, Pr.tapeOf (e₁Of (s k).2.1) (e₂Of (s k).2.1) ≠ none)
    (hpub : ∀ p, addrQ W Pr R N hN h B outputs x w s p ≠ W.pubBytes x) :
    realTest h B outputs (fsR1P W Pr N hN P Vp) adv x w (toRP W Pr R h B outputs x w hN s) =
      middleRealAbortV P h V B outputs (fsR1P W Pr N hN P Vp) (abR1P W N hN) adv x w
        (toMP W Pr eCm s) := by
  have hrun := run_eq_lazy W Pr R N hN h B outputs x w hin hc s
    (fun g g' hlt => hcoll _ _ (fun e => absurd ((posE W Pr N).injective e) (ne_of_lt hlt)))
    (fun g => hpub _)
  have hH : W.look (toRP W Pr R h B outputs x w hN s).1 = lookA R (TP W Pr R N hN h B outputs x w s) :=
    funext (look_toRP W Pr R N hN h B outputs x w s)
  have hfg := firstGood_eq W Pr R eCm N hN P Vp h V B outputs x w hV hin hc s hrun hexh
  -- the middle reads that are prover addresses are uncharged
  have hy : ∀ (i : Fin W.qmax) (p : Fin N × Pos1 Pr.E₁ Pr.E₂), addrQ W Pr R N hN h B outputs x w s p =
      qryQ W Pr eCm N hN P h V B outputs x w adv i s → ¬ chargedQ W Pr eCm N P h V w s p :=
    fun i p hp hch => hhit p i hch hp.symm
  have key : realGameP W Pr N P Vp h B outputs adv x w (toRP W Pr R h B outputs x w hN s) =
      (match accR W N P h V w (toMP W Pr eCm s) with
        | none => (abR1 W N hN).fail adv x (toMP W Pr eCm s).1
        | some k => (abR1 W N hN).extend adv x (toMP W Pr eCm s).1 k
            (view h B outputs x w (drawW W ((toMP W Pr eCm s).1 k)) ((toMP W Pr eCm s).2 k))) := by
    unfold realGameP
    dsimp only
    rw [hfg]
    rcases hacc : accR W N P h V w (toMP W Pr eCm s) with _ | k₀
    · dsimp only
      rw [fail_eqP W N hN adv x, hH]
      congr 1
      refine runLog_congr _ _ _ _ (fun e he => ?_)
      obtain ⟨i, hi⟩ := mem_runLog_idx _ _ _ e he
      have hq : qryQ W Pr eCm N hN P h V B outputs x w adv i s = e.1 := by
        unfold qryQ qryR advLogR
        rw [hacc]
        dsimp only
        rw [hi]
      exact oracle_none W Pr R eCm N hN P h V B outputs x w hin s (by exact hacc) e.1
        (fun p hp => hy i p (hp.trans hq.symm))
    · dsimp only
      rw [extend_eqP W N hN adv x, realOut_eq W Pr R N hN h B outputs x w hin hc s hrun k₀]
      have hv : (attOut W Pr h B outputs x w (lookA R (TP W Pr R N hN h B outputs x w s)) (s k₀).1
          (dS W Pr R N hN x s) (s k₀).2.1).view =
          view h B outputs x w (drawW W ((toMP W Pr eCm s).1 k₀)) ((toMP W Pr eCm s).2 k₀) := by
        show view h B outputs x w (chOf W (trOf (s k₀).2.1)) (tapeR W Pr (s k₀).2.1) = _
        rw [tape_eq W Pr eCm N s k₀ (hexh k₀)]
        rfl
      have hlog : (attOut W Pr h B outputs x w (lookA R (TP W Pr R N hN h B outputs x w s)) (s k₀).1
          (dS W Pr R N hN x s) (s k₀).2.1).log =
          verLog W x (view h B outputs x w (drawW W ((toMP W Pr eCm s).1 k₀)) ((toMP W Pr eCm s).2 k₀))
            ((toMP W Pr eCm s).1 k₀) := by
        rw [attOut_log W Pr R N hN h B outputs x w hin hc s hrun k₀,
          verLog_eq W Pr R eCm N hN h B outputs x w hcom s k₀ (hexh k₀)]
      rw [hv, hlog, hH]
      congr 2
      refine runLog_congr _ _ _ _ (fun e he => ?_)
      obtain ⟨i, hi⟩ := mem_runLog_idx _ _ _ e he
      have hq : qryQ W Pr eCm N hN P h V B outputs x w adv i s = e.1 := by
        unfold qryQ qryR advLogR
        rw [hacc]
        dsimp only
        rw [hi]
      exact oracle_acc W Pr R eCm N hN P h V B outputs x w hin hc hcom s hrun hcoll k₀ (by exact hacc) (hexh k₀) e.1
        (fun p hp => hy i p (hp.trans hq.symm))
  rw [real_eqP W Pr N hN P Vp h B outputs x w adv, middle_eqP W Pr N hN P Vp h V B outputs x w adv, key]
  rfl

end Agree

#print axioms tape_eq
#print axioms attOut_log
#print axioms verLog_eq
#print axioms realOut_eq
#print axioms oracle_acc
#print axioms oracle_none
#print axioms firstGood_eq
#print axioms agreeP
#print axioms lookup_none'
#print axioms lookup_some'
#print axioms fail_eqP
#print axioms extend_eqP
#print axioms mem_runLog_idx
#print axioms real_eqP
#print axioms middle_eqP
end R1Z.AgreeR1PBin
