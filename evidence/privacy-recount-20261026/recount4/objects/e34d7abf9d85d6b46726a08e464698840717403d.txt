import R1Z.QueryScanRealLazyBound

/-! The actual scan-specific event is transported from real randomness.
A conservative honest-program collision envelope is sufficient to bound it;
this file does not identify that envelope with E_fresh. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.QueryScanRealFreshMass
open R0P R0Z R0Z.JointView R0Z.FsStatement R0Z.FsAbort R0Z.FsGood R0Z.HvzkV R0Z.FsAbortBounds
  R1Z.GamesR1 R1Z.GamesR1PBin R1Z.CouplingR1PBin R1Z.LazyFrozen
  R1Z.AgreeR1PBin R1Z.EventsR1PBin R1Z.TranscriptR1 R1Z.LayoutR1PBin
  R1Z.QueryScanFreshInputs R1Z.QueryScanRealLazyBound
attribute [local instance] Classical.propDecidable

theorem issued_eq_final {m : ℕ}
    (a : Fin m → (Fin m → OracleAnswer) → List UInt8)
    (hc : ∀ i v v', (∀ j, j < i → v j = v' j) → a i v = a i v')
    (H : List UInt8 → OracleAnswer) (i : Fin m) :
    a i (runN a H 0 i.val) = a i (runC a H 0) := by
  apply hc
  intro j hj
  exact (runN_le a H 0 i.val m (le_of_lt i.isLt) j (Fin.lt_def.mp hj)).symm

def IsScan : TRead → Prop
  | .qb _ | .qa _ => True
  | _ => False

variable {K CommitHandle Aux : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K] {F : Subfield K}
variable (W : R1Wire K CommitHandle Aux) (Pr : R1ProverP K CommitHandle Aux F W)
  (R : RomModel W) (N : ℕ) (hN : 0 < N) (h : HonestProver K) (B : PackBasis F)
  (outputs : Statement K CommitHandle → Challenges K → Aux)
  (x : Statement K CommitHandle) (w : h.Instance)

def scanPosition (i : Fin (N * n1 W Pr)) : Prop :=
  match (posE W Pr N i).2 with
  | .inl j => IsScan j
  | .inr _ => False

/-- E_fresh on the actual real randomness. The digest is included once. -/
def realFresh (r : W.Tab × (Fin N → SecP)) : Prop :=
  FreshFailure (scanPosition W Pr N) (W.pubBytes x)
    (gAddr W Pr h B outputs x w r.2 (W.look r.1 (W.pubBytes x))) (W.look r.1)

include hN in
/-- Reusing scan inputs implies a lazy coupling exception. It does not follow
that every honest exception invalidates scan freshness. -/
theorem real_fresh_implies_lazy (hin : RAddrIn W Pr R h B outputs x w)
    (hc : RCausal W Pr h B outputs x w)
    (s : Fin N → AttS (F := F) W Pr) :
    realFresh W Pr N h B outputs x w (toRP W Pr R h B outputs x w hN s) →
      lazyBad W Pr R N hN h B outputs x w s := by
  intro he
  by_contra hn
  have hvec := real_vector_toRP W Pr R N hN h B outputs x w hin hc s hn
  have hs (i : Fin (N * n1 W Pr)) :
      gAddr W Pr h B outputs x w (toRP W Pr R h B outputs x w hN s).2
        (W.look (toRP W Pr R h B outputs x w hN s).1 (W.pubBytes x)) i
        (runN (gAddr W Pr h B outputs x w (toRP W Pr R h B outputs x w hN s).2
          (W.look (toRP W Pr R h B outputs x w hN s).1 (W.pubBytes x)))
          (W.look (toRP W Pr R h B outputs x w hN s).1) 0 i.val) =
        addrQ W Pr R N hN h B outputs x w s (posE W Pr N i) := by
    rw [issued_eq_final _ (gAddr_causal W Pr N h B outputs x w hc _ _) _ i]
    change gAddr W Pr h B outputs x w _ _ i
      (realVector W Pr N h B outputs x w (toRP W Pr R h B outputs x w hN s)) = _
    rw [hvec, look_toRP, TP_pub]
    exact (addrQ_posE W Pr R N hN h B outputs x w s i).symm
  obtain ⟨i, _, hp | ⟨j, hj, heq⟩⟩ := he
  · exact hn (Or.inr ⟨i, (hs i).symm.trans hp⟩)
  · exact hn (Or.inl ⟨j, i, hj, Or.inl trivial, (hs j).symm.trans (heq.trans (hs i))⟩)

include hN in
theorem real_fresh_mass (hin : RAddrIn W Pr R h B outputs x w)
    (hc : RCausal W Pr h B outputs x w) (hb : RCommitBytes W Pr)
    (hE₁ : Pr.E₁ ≤ 2^64) (hE₂ : Pr.E₂ ≤ 2^64) :
    eventMass (realFresh W Pr N h B outputs x w) ≤ lazyBudget (N * n1 W Pr) := by
  have hm := meanR_P W Pr R h B outputs x w N hN hc
    (fun r => if realFresh W Pr N h B outputs x w r then (1 : ℚ) else 0)
  have hm' : eventMass (fun s : Fin N → AttS (F := F) W Pr =>
      realFresh W Pr N h B outputs x w (toRP W Pr R h B outputs x w hN s)) =
      eventMass (realFresh W Pr N h B outputs x w) := by
    unfold eventMass
    convert hm using 1 <;> congr 1 <;> funext z <;> split_ifs <;> rfl
  rw [← hm']
  exact (eventMass_mono _ _ (real_fresh_implies_lazy W Pr R N hN h B outputs x w hin hc)).trans
    (lazy_bad_mass W Pr R N hN h B outputs x w hb hE₁ hE₂)

#print axioms issued_eq_final
#print axioms real_fresh_implies_lazy
#print axioms real_fresh_mass
end R1Z.QueryScanRealFreshMass
