import R1Z.EventsR1P4Bin

-- Binary-format copy of `R1Z.AgreeR1P` (LOG D76): the text is unchanged except that it is
-- built over `GamesR1PBin` / `LayoutR1P*Bin` (binary node index and `0x12 ‖ 2 children`).

/-! Agreement of the real and middle games, part 1 (DESIGN-R1-REAL §5): the
real run on the coupling.  Off collisions and off the digest address, the
honest in-order run against the reprogrammed table reads exactly the lazy
answers (`run_eq_lazy`), every read is answered by its own coordinate
(`ans_eq`), and the table is the base table at every other address
(`lookA_off`).  Generic: `runLog_congr`, lookup lemmas. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.AgreeR1PBin
open R0P R0Z R0Z.JointView R0Z.FsStatement R0Z.FsAbort R0Z.FsAbortBounds R0Z.HvzkV
  R1Z.Batched R1Z.LensR1 R1Z.TranscriptR1 R1Z.GamesR1 R1Z.LazyFrozen R1Z.GamesR1PBin
  R1Z.CouplingR1PBin R1Z.LayoutR1PBin R1Z.EventsR1PBin
attribute [local instance] Classical.propDecidable

/-! ### Generic list facts -/

theorem runLog_congr : ∀ (n : ℕ) (p : OProg) (O₁ O₂ : List UInt8 → OracleAnswer),
    (∀ e ∈ runLog p O₂ n, O₁ e.1 = O₂ e.1) → runLog p O₁ n = runLog p O₂ n
  | 0, p, _, _, _ => by cases p <;> rfl
  | n + 1, .done, _, _, _ => rfl
  | n + 1, .query a k, O₁, O₂, h => by
      have ha : O₁ a = O₂ a := h (a, O₂ a) List.mem_cons_self
      show (a, O₁ a) :: runLog (k (O₁ a)) O₁ n = (a, O₂ a) :: runLog (k (O₂ a)) O₂ n
      rw [ha, runLog_congr n (k (O₂ a)) O₁ O₂ (fun e he => h e (List.mem_cons_of_mem _ he))]

theorem length_runLog : ∀ (n : ℕ) (p : OProg) (O : List UInt8 → OracleAnswer),
    (runLog p O n).length ≤ n
  | 0, p, _ => by cases p <;> simp [runLog]
  | n + 1, .done, _ => by simp [runLog]
  | n + 1, .query a k, O => by
      show ((a, O a) :: runLog (k (O a)) O n).length ≤ n + 1
      simp only [List.length_cons]
      exact Nat.succ_le_succ (length_runLog n _ O)

theorem mem_getD {β : Type} (l : List β) (d : β) (q : ℕ) (hl : l.length ≤ q) (e : β) (he : e ∈ l) :
    ∃ i : Fin q, l.getD i.val d = e := by
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp he
  exact ⟨⟨i, lt_of_lt_of_le hi hl⟩, by simp [List.getD_eq_getElem?_getD, hi]⟩

theorem lookup_map_none {ι α β : Type} [BEq α] [LawfulBEq α] (f : ι → α) (g : ι → β) (y : α) :
    ∀ l : List ι, (∀ i ∈ l, f i ≠ y) → List.lookup y (l.map (fun i => (f i, g i))) = none
  | [], _ => rfl
  | i :: l, h => by
      rw [List.map_cons, List.lookup_cons]
      have hb : (y == f i) = false := by
        rw [beq_eq_false_iff_ne]
        exact fun e => h i List.mem_cons_self e.symm
      rw [hb]
      exact lookup_map_none f g y l (fun j hj => h j (List.mem_cons_of_mem _ hj))

theorem lookup_map_some {ι α β : Type} [BEq α] [LawfulBEq α] (f : ι → α) (g : ι → β) (y : α) (b : β) :
    ∀ l : List ι, (∃ i ∈ l, f i = y) → (∀ i ∈ l, f i = y → g i = b) →
      List.lookup y (l.map (fun i => (f i, g i))) = some b
  | [], ⟨_, hi, _⟩, _ => absurd hi List.not_mem_nil
  | i :: l, ⟨i₀, hi₀, he⟩, h => by
      rw [List.map_cons, List.lookup_cons]
      by_cases hyi : f i = y
      · have hb : (y == f i) = true := by rw [beq_iff_eq]; exact hyi.symm
        rw [hb, h i List.mem_cons_self hyi]
      · have hb : (y == f i) = false := by rw [beq_eq_false_iff_ne]; exact fun e => hyi e.symm
        rw [hb]
        rcases List.mem_cons.mp hi₀ with rfl | hl
        · exact absurd he hyi
        · exact lookup_map_some f g y b l ⟨i₀, hl, he⟩ (fun j hj => h j (List.mem_cons_of_mem _ hj))

variable {K CommitHandle Aux : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K] {F : Subfield K}

section Run
variable (W : R1Wire K CommitHandle Aux) (Pr : R1ProverP K CommitHandle Aux F W) (R : RomModel W)
  (N : ℕ) (hN : 0 < N) (h : HonestProver K) (B : PackBasis F)
  (outputs : Statement K CommitHandle → Challenges K → Aux) (x : Statement K CommitHandle)
  (w : h.Instance)

/-- Global read index ↦ read position. -/
def posE : Fin (N * n1 W Pr) ≃ Fin N × Pos1 Pr.E₁ Pr.E₂ :=
  finProdFinEquiv.symm.trans (Equiv.prodCongr (Equiv.refl _) Pr.ord)

theorem addrQ_posE (s : Fin N → AttS (F := F) W Pr) (g : Fin (N * n1 W Pr)) :
    addrQ W Pr R N hN h B outputs x w s (posE W Pr N g) =
      gAddr W Pr h B outputs x w (fun k => (s k).1) (dS W Pr R N hN x s) g (uVec W Pr s) := by
  show attAddr W Pr h B outputs x w (s (finProdFinEquiv.symm g).1).1 (dS W Pr R N hN x s)
      (s (finProdFinEquiv.symm g).1).2.1 (Pr.ord (finProdFinEquiv.symm g).2) =
    attAddr W Pr h B outputs x w (s (finProdFinEquiv.symm g).1).1 (dS W Pr R N hN x s)
      (attVec W Pr (uVec W Pr s) (finProdFinEquiv.symm g).1) (Pr.ord (finProdFinEquiv.symm g).2)
  rw [attVec_uVec]

theorem gAddr_causal (hc : RCausal W Pr h B outputs x w) (sec : Fin N → SecP) (d : OracleAnswer) :
    ∀ (g : Fin (N * n1 W Pr)) (V V' : Fin (N * n1 W Pr) → OracleAnswer), (∀ j, j < g → V j = V' j) →
      gAddr W Pr h B outputs x w sec d g V = gAddr W Pr h B outputs x w sec d g V' := by
  intro g V V' hV
  unfold gAddr
  refine hc _ _ _ _ _ (fun j hj => ?_)
  unfold attVec
  rw [Equiv.symm_apply_apply]
  refine hV _ ?_
  have hg : finProdFinEquiv ((finProdFinEquiv.symm g).1, (finProdFinEquiv.symm g).2) = g :=
    Equiv.apply_symm_apply _ _
  conv_rhs => rw [← hg]
  exact fPF_lt _ _ _ hj

/-- The base table and the reprogrammed table of the coupling. -/
def tP (s : Fin N → AttS (F := F) W Pr) : R.A → OracleAnswer := R.eTab (s ⟨0, hN⟩).2.2.2

def TP (s : Fin N → AttS (F := F) W Pr) : R.A → OracleAnswer :=
  progF (Frz R x) (aA W Pr R h B outputs x w (fun k => (s k).1)) (tP W Pr R N hN s) (uVec W Pr s)

theorem look_toRP (s : Fin N → AttS (F := F) W Pr) (b : List UInt8) :
    W.look (toRP W Pr R h B outputs x w hN s).1 b = lookA R (TP W Pr R N hN h B outputs x w s) b := by
  rw [look_eqA]
  show lookA R (R.eTab (R.eTab.symm _)) b = _
  rw [Equiv.apply_symm_apply]
  rfl

theorem TP_pub (s : Fin N → AttS (F := F) W Pr) :
    lookA R (TP W Pr R N hN h B outputs x w s) (W.pubBytes x) = dS W Pr R N hN x s :=
  lookA_frozen R x _ _ (fun y hy => progF_frozen _ _ _ _ y hy)

theorem run_eq_lazy (hin : RAddrIn W Pr R h B outputs x w) (hc : RCausal W Pr h B outputs x w)
    (s : Fin N → AttS (F := F) W Pr)
    (hcoll : ∀ g g' : Fin (N * n1 W Pr), g' < g →
      addrQ W Pr R N hN h B outputs x w s (posE W Pr N g') ≠ addrQ W Pr R N hN h B outputs x w s (posE W Pr N g))
    (hpub : ∀ g, addrQ W Pr R N hN h B outputs x w s (posE W Pr N g) ≠ W.pubBytes x) :
    runC (gAddr W Pr h B outputs x w (fun k => (s k).1) (dS W Pr R N hN x s))
      (lookA R (TP W Pr R N hN h B outputs x w s)) 0 = uVec W Pr s := by
  have hencA : ∀ g, R.enc (aA W Pr R h B outputs x w (fun k => (s k).1) g (uVec W Pr s) (tP W Pr R N hN s)) =
      addrQ W Pr R N hN h B outputs x w s (posE W Pr N g) := by
    intro g
    rw [enc_aA W Pr R h B outputs x w hin, addrQ_posE]
    rfl
  refine run_eqF (Frz R x) (aA W Pr R h B outputs x w (fun k => (s k).1))
    (causalF_aA W Pr R h B outputs x w hc _) (tP W Pr R N hN s) (uVec W Pr s) ?_ ?_ _ ?_
  · intro g hg
    unfold Frz at hg
    split at hg
    · next a ha =>
        have e := Finset.mem_singleton.mp hg
        apply hpub g
        rw [← hencA g, e]
        exact R.enc_of_dec _ _ ha
    · exact absurd hg (Finset.notMem_empty _)
  · intro g g' hlt heq
    apply hcoll g g' hlt
    rw [← hencA, ← hencA, heq]
  · intro g
    rw [runC_spec _ _ _ (gAddr_causal W Pr N h B outputs x w hc _ _) g]
    have e : gAddr W Pr h B outputs x w (fun k => (s k).1) (dS W Pr R N hN x s) g
        (runC (gAddr W Pr h B outputs x w (fun k => (s k).1) (dS W Pr R N hN x s))
          (lookA R (TP W Pr R N hN h B outputs x w s)) 0) =
        R.enc (aA W Pr R h B outputs x w (fun k => (s k).1) g
          (runC (gAddr W Pr h B outputs x w (fun k => (s k).1) (dS W Pr R N hN x s))
            (lookA R (TP W Pr R N hN h B outputs x w s)) 0) (TP W Pr R N hN h B outputs x w s)) := by
      rw [enc_aA W Pr R h B outputs x w hin, TP_pub]
    rw [e]
    unfold lookA
    rw [R.dec_enc]
    rfl

theorem ans_eq (hin : RAddrIn W Pr R h B outputs x w) (hc : RCausal W Pr h B outputs x w)
    (s : Fin N → AttS (F := F) W Pr)
    (hrun : runC (gAddr W Pr h B outputs x w (fun k => (s k).1) (dS W Pr R N hN x s))
      (lookA R (TP W Pr R N hN h B outputs x w s)) 0 = uVec W Pr s)
    (k : Fin N) (p : Pos1 Pr.E₁ Pr.E₂) :
    lookA R (TP W Pr R N hN h B outputs x w s) (addrQ W Pr R N hN h B outputs x w s (k, p)) = (s k).2.1 p := by
  have hp : posE W Pr N (finProdFinEquiv (k, Pr.ord.symm p)) = (k, p) := by
    simp [posE]
  have hs := runC_spec _ (lookA R (TP W Pr R N hN h B outputs x w s)) 0
    (gAddr_causal W Pr N h B outputs x w hc (fun k => (s k).1) (dS W Pr R N hN x s))
    (finProdFinEquiv (k, Pr.ord.symm p))
  rw [hrun, ← addrQ_posE, hp] at hs
  rw [← hs]
  simp [uVec]

theorem lookA_off (hin : RAddrIn W Pr R h B outputs x w) (s : Fin N → AttS (F := F) W Pr)
    (y : List UInt8) (hy : ∀ g, addrQ W Pr R N hN h B outputs x w s (posE W Pr N g) ≠ y) :
    lookA R (TP W Pr R N hN h B outputs x w s) y = lookA R (tP W Pr R N hN s) y := by
  unfold lookA
  split
  · next a ha =>
      refine progF_off _ _ _ _ _ (fun g e => hy g ?_)
      rw [← R.enc_of_dec _ _ ha, ← e, enc_aA W Pr R h B outputs x w hin, addrQ_posE]
      rfl
  · rfl

end Run

#print axioms runLog_congr
#print axioms length_runLog
#print axioms mem_getD
#print axioms lookup_map_none
#print axioms lookup_map_some
#print axioms addrQ_posE
#print axioms gAddr_causal
#print axioms look_toRP
#print axioms TP_pub
#print axioms run_eq_lazy
#print axioms ans_eq
#print axioms lookA_off
end R1Z.AgreeR1PBin
