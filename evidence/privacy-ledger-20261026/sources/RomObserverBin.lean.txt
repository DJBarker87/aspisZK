import R1Z.RomFiniteBin

/-! The classical observer map keeps the entire decision function. Only
its adaptive query program is supplied by the source operational handoff. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.RomObserverBin
open R0P R0Z R0Z.JointView R0Z.FsStatement R0Z.FsAbortBounds
  R1Z.Batched R1Z.GamesR1 R1Z.GamesR1PBin R1Z.RomFiniteBin R1Z.LazyFrozen
attribute [local instance] Classical.propDecidable

/-- No bound on the size of the table is computed by reduction. The existing
frozen lazy programming law applies to the concrete finite byte carrier. -/
theorem lazy_table_uniform (bound : ℕ) (frozen : Finset (Address bound)) {m : ℕ}
    (a : Fin m → (Fin m → OracleAnswer) → (Address bound → OracleAnswer) → Address bound)
    (causal : CausalF frozen a) (f : (Address bound → OracleAnswer) → ℚ) :
    mean (fun p : (Address bound → OracleAnswer) × (Fin m → OracleAnswer) =>
      f (progF frozen a p.1 p.2)) = mean f := mean_progF frozen a causal f

/-- The cap counts query calls, including repeats, on every branch. -/
theorem runLog_length (program : OProg) (oracle : List UInt8 → OracleAnswer) (fuel : ℕ) :
    (runLog program oracle fuel).length ≤ fuel := by
  induction fuel generalizing program with
  | zero => cases program <;> simp only [runLog, List.length_nil, Nat.le_refl]
  | succ n ih =>
      cases program with
      | done => simp only [runLog, List.length_nil, Nat.zero_le]
      | query a k =>
          simpa only [runLog, List.length_cons] using Nat.succ_le_succ (ih (k (oracle a)))

variable {K CommitHandle Aux : Type} [Field K] {F : Subfield K}

def observerMap (source : FSExperiments K CommitHandle Aux R1Bat F)
    (program : source.Adversary → View K CommitHandle Aux R1Bat →
      List (List UInt8 × OracleAnswer) → OProg) (adv : source.Adversary) :
    R1Adv K CommitHandle Aux :=
  ⟨program adv, source.observe adv⟩

theorem observer_preserved (source : FSExperiments K CommitHandle Aux R1Bat F)
    (program : source.Adversary → View K CommitHandle Aux R1Bat →
      List (List UInt8 × OracleAnswer) → OProg) (adv : source.Adversary)
    (rv : ROMView K CommitHandle Aux R1Bat) :
    (observerMap source program adv).decide rv = source.observe adv rv := rfl

theorem capped_queries (base : R1Wire K CommitHandle Aux) (bound : ℕ)
    (program : OProg) (tab : (wire base bound).Tab) :
    (runLog program ((wire base bound).look tab) (wire base bound).qmax).length ≤ 2^64 :=
  runLog_length program _ _

variable [Fintype K] [DecidableEq K] [Algebra (ZMod AspisCircleGroupOrder.P) K]

theorem model_observer_preserved (base : R1Wire K CommitHandle Aux) (bound : ℕ)
    (Pr : R1ProverP K CommitHandle Aux F (wire base bound)) (N : ℕ) (hN : 0 < N)
    (P : Challenges K → Prop) (Vp : (h : HonestProver K) → Challenges K → h.Instance → Prop)
    (source : FSExperiments K CommitHandle Aux R1Bat F)
    (program : source.Adversary → View K CommitHandle Aux R1Bat →
      List (List UInt8 × OracleAnswer) → OProg) (adv : source.Adversary)
    (rv : ROMView K CommitHandle Aux R1Bat) :
    (fsR1P (wire base bound) Pr N hN P Vp).observe (observerMap source program adv) rv =
      source.observe adv rv := rfl

#print axioms lazy_table_uniform
#print axioms runLog_length
#print axioms observer_preserved
#print axioms capped_queries
#print axioms model_observer_preserved
end R1Z.RomObserverBin
