import R1Z.ProverCommitGlobal42

/-! Concrete honest global read execution under conditional programming.
Public memo coherence replaces public freshness. Private freshness and pair
separation remain explicit bad-event complements, not trusted callbacks. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverCommitGlobalRun42
open R0P R0Z R0Z.JointView R0Z.FsStatement R0Z.FsAbort R0Z.HvzkV
open GamesR1 GamesR1PBin CouplingR1PBin AgreeR1PBin LayoutR1PBin LensR1 LazyFrozen
open ProverCommitGlobal42
attribute [local instance] Classical.propDecidable
variable {K CommitHandle Aux : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K] {F : Subfield K}
variable (W : R1Wire K CommitHandle Aux) (Pr : R1ProverP K CommitHandle Aux F W)
  (R : RomModel W) (h : HonestProver K) (B : PackBasis F)
  (outputs : Statement K CommitHandle → Challenges K → Aux)
  (x : Statement K CommitHandle) (w : h.Instance)

def table {N : Nat} (Fr : Finset R.A) (sec : Fin N → SecP)
    (answers : Fin N → Fin 2 → OracleAnswer) (base : R.A → OracleAnswer)
    (coins : Fin (N*n1 W Pr) → OracleAnswer) : R.A → OracleAnswer :=
  progF Fr (ProverCommitPublicCoins41.addresses (positions W Pr N) (values W Pr answers)
    (aA W Pr R h B outputs x w sec)) base coins

theorem run_eq (hin : RAddrIn W Pr R h B outputs x w)
    (hc : RCausal W Pr h B outputs x w) (Fr : Finset R.A) (covers : Frz R x ⊆ Fr)
    {N : Nat} (sec : Fin N → SecP) (answers : Fin N → Fin 2 → OracleAnswer)
    (base : R.A → OracleAnswer) (coins : Fin (N*n1 W Pr) → OracleAnswer)
    (memo : ∀ i, i ∈ positions W Pr N →
      aA W Pr R h B outputs x w sec i (normalized W Pr answers coins) base ∈ Fr ∧
      values W Pr answers i = base (aA W Pr R h B outputs x w sec i (normalized W Pr answers coins) base))
    (fresh : ∀ i, i ∉ positions W Pr N →
      aA W Pr R h B outputs x w sec i (normalized W Pr answers coins) base ∉ Fr)
    (distinct : ∀ i, i ∉ positions W Pr N → ∀ j, j < i →
      aA W Pr R h B outputs x w sec j (normalized W Pr answers coins) base ≠
      aA W Pr R h B outputs x w sec i (normalized W Pr answers coins) base) :
    let programmed := table W Pr R h B outputs x w Fr sec answers base coins
    runC (gAddr W Pr h B outputs x w sec (lookA R programmed (W.pubBytes x)))
      (lookA R programmed) 0 = normalized W Pr answers coins := by
  let a := aA W Pr R h B outputs x w sec
  let programmed := table W Pr R h B outputs x w Fr sec answers base coins
  have stable : ∀ y ∈ Fr, programmed y = base y := fun y hy => progF_frozen Fr _ base coins y hy
  have digest : lookA R programmed (W.pubBytes x) = lookA R base (W.pubBytes x) :=
    lookA_frozen R x programmed base (fun y hy => stable y (covers hy))
  let actual := runC (gAddr W Pr h B outputs x w sec (lookA R programmed (W.pubBytes x)))
    (lookA R programmed) 0
  have ca : CausalF Fr a := by
    intro i u v t s prior same
    exact causalF_aA W Pr R h B outputs x w hc sec i u v t s prior (fun y hy => same y (covers hy))
  apply ProverCommitPublicCoins41.run_eq Fr (positions W Pr N) (values W Pr answers)
    a ca base coins actual memo fresh distinct
  intro i
  change actual i = programmed (a i actual programmed)
  have spec := runC_spec _ (lookA R programmed) 0
    (gAddr_causal W Pr N h B outputs x w hc sec (lookA R programmed (W.pubBytes x))) i
  change actual i = lookA R programmed
    (gAddr W Pr h B outputs x w sec (lookA R programmed (W.pubBytes x)) i actual) at spec
  rw [spec]
  have enc := enc_aA W Pr R h B outputs x w hin sec i actual programmed
  rw [←enc]
  simp only [lookA,R.dec_enc]
  rfl

/-- Any later observation of the successful read vector, including ordered
publication, retained retry history and ledger state, transports pointwise.
The theorem supplies the run equation rather than assuming one. -/
theorem continuation (hin : RAddrIn W Pr R h B outputs x w)
    (hc : RCausal W Pr h B outputs x w) (Fr : Finset R.A) (covers : Frz R x ⊆ Fr)
    {N : Nat} (sec : Fin N → SecP) (answers : Fin N → Fin 2 → OracleAnswer)
    (base : R.A → OracleAnswer) (coins : Fin (N*n1 W Pr) → OracleAnswer)
    (memo : ∀ i, i ∈ positions W Pr N →
      aA W Pr R h B outputs x w sec i (normalized W Pr answers coins) base ∈ Fr ∧
      values W Pr answers i = base (aA W Pr R h B outputs x w sec i (normalized W Pr answers coins) base))
    (fresh : ∀ i, i ∉ positions W Pr N →
      aA W Pr R h B outputs x w sec i (normalized W Pr answers coins) base ∉ Fr)
    (distinct : ∀ i, i ∉ positions W Pr N → ∀ j, j < i →
      aA W Pr R h B outputs x w sec j (normalized W Pr answers coins) base ≠
      aA W Pr R h B outputs x w sec i (normalized W Pr answers coins) base)
    {State Observation : Type} (state : State)
    (publish : (Fin (N*n1 W Pr) → OracleAnswer) → State → Observation) :
    let programmed := table W Pr R h B outputs x w Fr sec answers base coins
    publish (runC (gAddr W Pr h B outputs x w sec (lookA R programmed (W.pubBytes x)))
      (lookA R programmed) 0) state = publish (normalized W Pr answers coins) state := by
  dsimp only
  rw [run_eq W Pr R h B outputs x w hin hc Fr covers sec answers base coins memo fresh distinct]

#print axioms run_eq
#print axioms continuation
end R1Z.ProverCommitGlobalRun42
