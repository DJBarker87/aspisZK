import R1Z.RomObserverBin
import R1Z.QueryScanHistorySplit
/-! Identity of the actual observer of the constructed model. This is not
an identification of any shipped Rust execution with that model. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverCommitFixedObserver
open R0P R0Z R0Z.JointView R0Z.FsStatement R0Z.FsAbort
  R1Z.Batched R1Z.GamesR1 R1Z.GamesR1PBin R1Z.QueryScanHistorySplit
variable {K CommitHandle Aux : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K] {F : Subfield K}
variable (W : R1Wire K CommitHandle Aux) (Pr : R1ProverP K CommitHandle Aux F W)
variable (N : Nat) (hN : 0 < N) (P : Challenges K → Prop)
  (Vp : (h : HonestProver K) → Challenges K → h.Instance → Prop)

theorem observer_identity (adv : (fsR1P W Pr N hN P Vp).Adversary) :
    RomObserverBin.observerMap (fsR1P W Pr N hN P Vp) (fun a => a.prog) adv = adv := by
  cases adv
  rfl

/-- Agreement everywhere, hence outside any fixed real or ideal bad event.
The bad event is not replaced or enlarged. -/
def self_join {R : Type} [Fintype R] [Nonempty R]
    (f : R → ℚ) (bad : Fin 8 → R → Prop) : ModelExecutionJoin f f bad where
  cp := idCoupling R
  agreement := fun _ _ => rfl

#print axioms observer_identity
#print axioms self_join
end R1Z.ProverCommitFixedObserver
