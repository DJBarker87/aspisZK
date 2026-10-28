import R1Z.EventsR1PBin
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Option
import Mathlib.Logic.Equiv.Option

-- Binary-format copy of `R1Z.EventsR1P2` (LOG D76): the text is unchanged except that it is
-- built over `GamesR1PBin` / `LayoutR1P*Bin` (binary node index and `0x12 ‖ 2 children`).

/-! Events and freshness, part 2 (DESIGN-R1-REAL §5): positions, addresses,
charging, adversary reads; the update lemmas for every designated-field lens. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.EventsR1PBin
open R0P R0Z R0Z.JointView R0Z.FsStatement R0Z.FsAbort R0Z.FsAbortBounds R0Z.HvzkV
  R1Z.Batched R1Z.LensR1 R1Z.TranscriptR1 R1Z.GamesR1 R1Z.LazyFrozen R1Z.GamesR1PBin
  R1Z.CouplingR1PBin R1Z.LayoutR1PBin
attribute [local instance] Classical.propDecidable

variable {K CommitHandle Aux : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K] {F : Subfield K}

/-- `card_NZ` for any `Fintype NZ` instance (LOG D68.3): counted through
`Option NZ ≃ OracleAnswer` (`Equiv.optionSubtypeNe 0`) and `card_ans`.  The only
cross-module instance (the one `card_ans` was elaborated with) enters through
`Subsingleton (Fintype _)`, so no two instances are compared by reduction. -/
theorem card_NZ_of (i : Fintype NZ) : 2 ^ 255 ≤ @Fintype.card NZ i := by
  have hA : ∀ j : Fintype OracleAnswer, @Fintype.card OracleAnswer j = 2 ^ 256 := fun j =>
    (congrArg (@Fintype.card OracleAnswer) (Subsingleton.elim j _)).trans card_ans
  have e : Option NZ ≃ OracleAnswer := Equiv.optionSubtypeNe (0 : OracleAnswer)
  have h2 : Fintype.card NZ + 1 = 2 ^ 256 := by
    rw [← Fintype.card_option, Fintype.card_congr e]
    exact hA _
  have : (2 : ℕ) ^ 255 < 2 ^ 256 := Nat.pow_lt_pow_right (by norm_num) (by norm_num)
  omega

theorem card_NZ : 2 ^ 255 ≤ Fintype.card NZ := card_NZ_of _

def nzOf (a : OracleAnswer) : NZ := if hz : a ≠ 0 then ⟨a, hz⟩ else Classical.arbitrary NZ

theorem nzOf_val (z : NZ) : nzOf z.1 = z := by
  unfold nzOf
  rw [dif_pos z.2]

section Ev
variable (W : R1Wire K CommitHandle Aux) (Pr : R1ProverP K CommitHandle Aux F W) (R : RomModel W)
  (eCm : W.Cm ≃ (RIdx → OracleAnswer)) (N : ℕ) (hN : 0 < N) (P : Challenges K → Prop)
  (h : HonestProver K) (V : Challenges K → h.Instance → Prop) (B : PackBasis F)
  (outputs : Statement K CommitHandle → Challenges K → Aux) (x : Statement K CommitHandle)
  (w : h.Instance) (adv : R1Adv K CommitHandle Aux)

/-- The statement digest on the coupling space (attempt 0's table is the base table). -/
def dS (s : Fin N → AttS (F := F) W Pr) : OracleAnswer :=
  lookA R (R.eTab (s ⟨0, hN⟩).2.2.2) (W.pubBytes x)

/-- The address of position `p` on the lazy answers. -/
def addrQ (s : Fin N → AttS (F := F) W Pr) (p : Fin N × Pos1 Pr.E₁ Pr.E₂) : List UInt8 :=
  attAddr W Pr h B outputs x w (s p.1).1 (dS W Pr R N hN x s) (s p.1).2.1 p.2

def accM (s : Fin N → AttS (F := F) W Pr) : Option (Fin N) := accR W N P h V w (toMP W Pr eCm s)

/-- Commitment position `c` of attempt `k` is opened by the verifier. -/
def pubC (s : Fin N → AttS (F := F) W Pr) (k : Fin N) (c : CPos Pr.E₁ Pr.E₂) : Prop :=
  c ∈ (Pr.openList (chOf W (trOf (s k).2.1))).map cposOf

/-- Charged: not published by the accepted attempt. -/
def chargedQ (s : Fin N → AttS (F := F) W Pr) : Fin N × Pos1 Pr.E₁ Pr.E₂ → Prop
  | (k, .inl _) => accM W Pr eCm N P h V w s ≠ some k
  | (k, .inr c) => ¬ (accM W Pr eCm N P h V w s = some k ∧ pubC W Pr N s k c)

def qryQ (i : Fin W.qmax) (s : Fin N → AttS (F := F) W Pr) : List UInt8 :=
  qryR W N hN P h V B outputs x w adv i (toMP W Pr eCm s)

/-! ### Block lenses that leave the table and the tape alone -/

/-- A block lens of attempt `k` that moves neither the spare tape, the table,
nor the expander answers. -/
structure Tame {U : Type} (L : Lens (AttS (F := F) W Pr) U) : Prop where
  tail : ∀ a u, (L.set a u).2.2 = a.2.2
  e₁ : ∀ a u, e₁Of (L.set a u).2.1 = e₁Of a.2.1
  e₂ : ∀ a u, e₂Of (L.set a u).2.1 = e₂Of a.2.1
  ch : ∀ a u, chOf (K := K) W (trOf (L.set a u).2.1) = chOf W (trOf a.2.1)

theorem dS_tame {U : Type} (L : Lens (AttS (F := F) W Pr) U) (hL : Tame W Pr L) (k : Fin N)
    (s : Fin N → AttS (F := F) W Pr) (u : U) :
    dS W Pr R N hN x ((Lens.fnAt k L).set s u) = dS W Pr R N hN x s := by
  unfold dS
  by_cases hk : (⟨0, hN⟩ : Fin N) = k
  · rw [hk, Lens.fnAt_set_eq, hL.tail]
  · rw [Lens.fnAt_set_ne _ _ _ _ _ hk]

theorem accM_tame {U : Type} (L : Lens (AttS (F := F) W Pr) U) (hL : Tame W Pr L) (k : Fin N)
    (s : Fin N → AttS (F := F) W Pr) (u : U) :
    accM W Pr eCm N P h V w ((Lens.fnAt k L).set s u) = accM W Pr eCm N P h V w s := by
  unfold accM accR
  have e1 : ∀ ct : (Fin N → R1Coins W.Cm W.Tab) × (Fin N → Tape K F),
      firstGood (fun c => P (drawW W c) ∧ V (drawW W c) w) ct.1 =
        firstGood (fun j => P (drawW W (ct.1 j)) ∧ V (drawW W (ct.1 j)) w) id := fun _ => rfl
  rw [e1, e1]
  apply firstGood_congr
  intro j
  show P (chOf W (trOf (((Lens.fnAt k L).set s u) j).2.1)) ∧ V (chOf W (trOf (((Lens.fnAt k L).set s u) j).2.1)) w ↔
    P (chOf W (trOf (s j).2.1)) ∧ V (chOf W (trOf (s j).2.1)) w
  by_cases hj : j = k
  · rw [hj, Lens.fnAt_set_eq, hL.ch]
  · rw [Lens.fnAt_set_ne _ _ _ _ _ hj]

theorem pubC_tame {U : Type} (L : Lens (AttS (F := F) W Pr) U) (hL : Tame W Pr L) (k : Fin N)
    (s : Fin N → AttS (F := F) W Pr) (u : U) (k' : Fin N) (c : CPos Pr.E₁ Pr.E₂) :
    pubC W Pr N ((Lens.fnAt k L).set s u) k' c ↔ pubC W Pr N s k' c := by
  unfold pubC
  by_cases hk : k' = k
  · rw [hk, Lens.fnAt_set_eq, hL.ch]
  · rw [Lens.fnAt_set_ne _ _ _ _ _ hk]

theorem charged_tame {U : Type} (L : Lens (AttS (F := F) W Pr) U) (hL : Tame W Pr L) (k : Fin N)
    (s : Fin N → AttS (F := F) W Pr) (u : U) (p : Fin N × Pos1 Pr.E₁ Pr.E₂) :
    chargedQ W Pr eCm N P h V w ((Lens.fnAt k L).set s u) p ↔ chargedQ W Pr eCm N P h V w s p := by
  obtain ⟨k', q | c⟩ := p
  · show accM W Pr eCm N P h V w ((Lens.fnAt k L).set s u) ≠ some k' ↔ _
    rw [accM_tame W Pr eCm N P h V w L hL]
    rfl
  · show ¬ (accM W Pr eCm N P h V w ((Lens.fnAt k L).set s u) = some k' ∧
      pubC W Pr N ((Lens.fnAt k L).set s u) k' c) ↔ _
    rw [accM_tame W Pr eCm N P h V w L hL, pubC_tame W Pr N L hL]
    rfl

theorem toMP_tame_tape {U : Type} (L : Lens (AttS (F := F) W Pr) U) (hL : Tame W Pr L) (k : Fin N)
    (s : Fin N → AttS (F := F) W Pr) (u : U) :
    (toMP W Pr eCm ((Lens.fnAt k L).set s u)).2 = (toMP W Pr eCm s).2 := by
  funext j
  show (Pr.tapeOf (e₁Of (((Lens.fnAt k L).set s u) j).2.1) (e₂Of (((Lens.fnAt k L).set s u) j).2.1)).getD
      (((Lens.fnAt k L).set s u) j).2.2.1 = _
  by_cases hj : j = k
  · rw [hj, Lens.fnAt_set_eq, hL.e₁, hL.e₂, hL.tail]
    rfl
  · rw [Lens.fnAt_set_ne _ _ _ _ _ hj]
    rfl

theorem toMP_tame_other {U : Type} (L : Lens (AttS (F := F) W Pr) U) (k : Fin N)
    (s : Fin N → AttS (F := F) W Pr) (u : U) (j : Fin N) (hj : j ≠ k) :
    (toMP W Pr eCm ((Lens.fnAt k L).set s u)).1 j = (toMP W Pr eCm s).1 j := by
  show (gM W Pr eCm (((Lens.fnAt k L).set s u) j)).1 = (gM W Pr eCm (s j)).1
  rw [Lens.fnAt_set_ne _ _ _ _ _ hj]

theorem toMP_tame_tab {U : Type} (L : Lens (AttS (F := F) W Pr) U) (hL : Tame W Pr L) (k : Fin N)
    (s : Fin N → AttS (F := F) W Pr) (u : U) (j : Fin N) :
    ((toMP W Pr eCm ((Lens.fnAt k L).set s u)).1 j).2.2.2 = ((toMP W Pr eCm s).1 j).2.2.2 := by
  show (((Lens.fnAt k L).set s u) j).2.2.2 = (s j).2.2.2
  by_cases hj : j = k
  · rw [hj, Lens.fnAt_set_eq, hL.tail]
  · rw [Lens.fnAt_set_ne _ _ _ _ _ hj]

theorem toMP_tame_draw {U : Type} (L : Lens (AttS (F := F) W Pr) U) (hL : Tame W Pr L) (k : Fin N)
    (s : Fin N → AttS (F := F) W Pr) (u : U) (j : Fin N) :
    drawW (K := K) W ((toMP W Pr eCm ((Lens.fnAt k L).set s u)).1 j) = drawW W ((toMP W Pr eCm s).1 j) := by
  show chOf W (trOf (((Lens.fnAt k L).set s u) j).2.1) = chOf W (trOf (s j).2.1)
  by_cases hj : j = k
  · rw [hj, Lens.fnAt_set_eq, hL.ch]
  · rw [Lens.fnAt_set_ne _ _ _ _ _ hj]

/-- The adversary's middle log depends only on the acceptance, the accepted
attempt's draw, tape and verifier log, and the base table. -/
theorem advLogR_congr (ct ct' : (Fin N → R1Coins W.Cm W.Tab) × (Fin N → Tape K F))
    (hacc : accR W N P h V w ct' = accR W N P h V w ct)
    (htab : (ct'.1 ⟨0, hN⟩).2.2.2 = (ct.1 ⟨0, hN⟩).2.2.2)
    (hk : ∀ k₀, accR W N P h V w ct = some k₀ →
      drawW (K := K) W (ct'.1 k₀) = drawW W (ct.1 k₀) ∧ ct'.2 k₀ = ct.2 k₀ ∧
      verLog W x (view h B outputs x w (drawW W (ct.1 k₀)) (ct.2 k₀)) (ct'.1 k₀) =
        verLog W x (view h B outputs x w (drawW W (ct.1 k₀)) (ct.2 k₀)) (ct.1 k₀)) :
    advLogR W N hN P h V B outputs x w adv ct' = advLogR W N hN P h V B outputs x w adv ct := by
  unfold advLogR
  rw [hacc]
  rcases hA : accR W N P h V w ct with _ | k₀
  · simp only [htab]
  · obtain ⟨hd, ht, hv⟩ := hk k₀ hA
    simp only
    rw [hd, ht]
    unfold progOracle
    rw [hv, htab]

/-! ### The chain lenses are tame -/

theorem tame_chain (c : Coord) (hc : ChainC c) : Tame W Pr (chainL W Pr c) := by
  cases c with
  | root =>
      refine ⟨fun a u => rfl, fun a u => ?_, fun a u => ?_, fun a u => ?_⟩
      · funext c; simp [e₁Of, e₂Of, chainL, vL, selL, Function.update_apply]
      · funext c; simp [e₁Of, e₂Of, chainL, vL, selL, Function.update_apply]
      · show chOf W (trOf (Function.update a.2.1 (.inr (.inl 0)) u)) = _
        rw [trOf_update_root]
  | sel =>
      refine ⟨fun a u => rfl, fun a u => ?_, fun a u => ?_, fun a u => ?_⟩
      · funext c; simp [e₁Of, e₂Of, chainL, vL, selL, Function.update_apply]
      · funext c; simp [e₁Of, e₂Of, chainL, vL, selL, Function.update_apply]
      · show chOf W (trOf (Function.update a.2.1 (.inl (.qa (ksV W Pr a.2.1))) u)) = _
        rw [trOf_update_tr]
        exact chOf_update_tr W _ (TRead.qa (ksV W Pr a.2.1)) (fun h => h) u
  | ans j =>
      refine ⟨fun a u => rfl, fun a u => ?_, fun a u => ?_, fun a u => ?_⟩
      · funext c; simp [e₁Of, e₂Of, chainL, vL, selL, Function.update_apply]
      · funext c; simp [e₁Of, e₂Of, chainL, vL, selL, Function.update_apply]
      · show chOf W (trOf (Function.update a.2.1 (.inl j) u)) = _
        rw [trOf_update_tr]
        exact chOf_update_tr W _ _ (hc j rfl) u

theorem tame_sec (i : Fin 3) : Tame W Pr (secL W Pr i) :=
  ⟨fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl⟩

theorem tame_rest (q : RIdx) : Tame W Pr (vL W Pr (.inr (.inr (.inr q)))) := by
  refine ⟨fun a u => rfl, fun a u => ?_, fun a u => ?_, fun a u => ?_⟩
  · funext c; simp [e₁Of, e₂Of, vL, Function.update_apply]
  · funext c; simp [e₁Of, e₂Of, vL, Function.update_apply]
  · show chOf W (trOf (Function.update a.2.1 (.inr (.inr (.inr q))) u)) = _
    congr 1

end Ev

#print axioms card_NZ_of
#print axioms card_NZ
#print axioms nzOf_val
#print axioms dS_tame
#print axioms accM_tame
#print axioms charged_tame
#print axioms toMP_tame_tape
#print axioms toMP_tame_other
#print axioms toMP_tame_tab
#print axioms toMP_tame_draw
#print axioms advLogR_congr
#print axioms tame_chain
#print axioms tame_sec
#print axioms tame_rest
#print axioms pubC_tame
end R1Z.EventsR1PBin
