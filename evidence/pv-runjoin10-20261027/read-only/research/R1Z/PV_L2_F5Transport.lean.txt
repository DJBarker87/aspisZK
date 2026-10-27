import R1Z.PV_L2_F5
import R1Z.ProverCommitQuotientCoupling

/-! Real-to-lazy QueryScan transport and joint preservation across concrete
quotient tape completion. This is not yet the witness-absorption/simE leg. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_L2_F5Transport
open R0P R0Z R0Z.JointView R0Z.FsStatement R0Z.FsAbort R0Z.FsAbortBounds
  R0Z.HvzkV R1Z.Batched R1Z.GamesR1 R1Z.GamesR1PBin R1Z.LensR1 R1Z.TranscriptR1
  R1Z.LazyFrozen R1Z.CouplingR1PBin R1Z.AgreeR1PBin R1Z.EventsR1PBin R1Z.FinalR1PBin
  R1Z.LayoutR1PBin R1Z.QueryScanPrivacyFinal R1Z.QueryScanRealLazyBound
  R1Z.ProverCommitQuotientCoupling
attribute [local instance] Classical.propDecidable
variable {K CommitHandle Aux : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K] {F : Subfield K}
variable (W : R1Wire K CommitHandle Aux) (Pr : R1ProverP K CommitHandle Aux F W)
  (R : RomModel W) (N : Nat) (hN : 0 < N) (h : HonestProver K) (B : PackBasis F)
  (outputs : Statement K CommitHandle → Challenges K → Aux)
  (x : Statement K CommitHandle) (w : h.Instance)

def vectorHistory (v : Fin (N * n1 W Pr) → OracleAnswer) :=
  fun k : Fin N => PV_L2_F5.history (fun j => attVec W Pr v k (.inl (.qb j)))

theorem real_to_lazy (hin : RAddrIn W Pr R h B outputs x w)
    (hc : RCausal W Pr h B outputs x w)
    (s : Fin N → AttS (F := F) W Pr)
    (hn : ¬ lazyBad W Pr R N hN h B outputs x w s) :
    vectorHistory W Pr N (realVector W Pr N h B outputs x w
      (toRP W Pr R h B outputs x w hN s)) =
      (fun k => PV_L2_F5.history (fun j => (s k).2.1 (.inl (.qb j)))) := by
  rw [real_vector_toRP W Pr R N hN h B outputs x w hin hc s hn]
  unfold vectorHistory
  simp only [attVec_uVec]

/-- This observation is definable on the actual middle coins, independently
of the mask tape. It retains the full raw query-block prefix. -/
def coinHistory (c : R1Coins W.Cm W.Tab) := PV_L2_F5.history (fun j => c.1 (.qb j))

variable (eCm : W.Cm ≃ (RIdx → OracleAnswer))

theorem lazy_to_middle (s : Fin N → AttS (F := F) W Pr) :
    (fun k => PV_L2_F5.history (fun j => (s k).2.1 (.inl (.qb j)))) =
      (fun k => coinHistory W ((toMP W Pr eCm s).1 k)) := by
  rfl

theorem completion_joint (ch : Challenges K) (a : AttS (F := F) W Pr) :
    (coinHistory W (gMQ W Pr eCm a).1,
      view (Bat := R1Bat) h B outputs x w ch (gMQ W Pr eCm a).2) =
    (coinHistory W (gM W Pr eCm a).1,
      view h B outputs x w ch (gM W Pr eCm a).2) := by
  have hv := completed_view W Pr eCm h B outputs x w ch a
  exact Prod.ext rfl hv

#print axioms real_to_lazy
#print axioms lazy_to_middle
#print axioms completion_joint
end R1Z.PV_L2_F5Transport
