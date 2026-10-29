import R1Z.PV_RunJoin_NativeAttemptPublication55
import R1Z.PV_RunJoin_CommonOracle51
/-! Conditional specialization of the full native attempt to the original
completed toRP table. The six fixed links remain hypotheses. This does not
identify stored records or prove common-sample producer association. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_NativeToRP55
open Aeneas Aeneas.Std Result ProverRwFull PV_RunJoin_WeightInstalled46
open R0P R0Z R0Z.JointView R0Z.FsStatement R0Z.HvzkV
open R1Z.GamesR1 R1Z.GamesR1PBin R1Z.CouplingR1PBin R1Z.TranscriptR1 R1Z.EventsR1PBin
open PV_RunJoin_PublishSkeleton54
open PV_RunJoin_NativeControl55 (Phase)
variable {K CH Aux : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K] {F : Subfield K}

variable (W : R1Wire K CH Aux) (Pr : R1ProverP K CH Aux F W) (R : RomModel W)
  (N : Nat) (hN : 0<N) (h : R0Z.ZkStatement.HonestProver K) (B : PackBasis F)
  (outputs : Statement K CH → Challenges K → Aux) (x : Statement K CH) (w : h.Instance)
  (s : Fin N → AttS (F:=F) W Pr)

theorem complete (base : ExternalTypes) (heap : Heap) (box : Box)
    (ops : @ExternalFuns (types base))
    (data : @Phase (types base) → PV_RunJoin_OpeningImages54.Data)
    (plans : @Phase (types base) → Plan)
    (common : @PV_RunJoin_Link_CommonSample (types base) (selected base heap box ops) (@Phase (types base)) (@PV_RunJoin_NativeCallback55.runOf (types base) data plans))
    (backend : @PV_RunJoin_Link_BackendInput (types base) (selected base heap box ops) (@Phase (types base)) (@PV_RunJoin_NativeCallback55.runOf (types base) data plans))
    (finish : @PV_RunJoin_Link_FinishContext (types base) (selected base heap box ops) (@Phase (types base)) (@PV_RunJoin_NativeCallback55.runOf (types base) data plans))
    (query : @PV_RunJoin_Link_QueryAppend (types base) (selected base heap box ops) (@Phase (types base)) (@PV_RunJoin_NativeCallback55.runOf (types base) data plans))
    (node : @PV_RunJoin_Link_NodeAppend (types base) (selected base heap box ops) (@Phase (types base)) (@PV_RunJoin_NativeCallback55.runOf (types base) data plans))
    (ordering : @PV_RunJoin_Link_PublishOrder (types base) (selected base heap box ops) (@Phase (types base)) (@PV_RunJoin_NativeCallback55.runOf (types base) data plans))
 :
    PV_RJ4IDB.OpenInputs.RUNJOIN_PUBLISH_COMPACT
      (fun i : @PV_RunJoin_NativeAttemptPublication55.Input (types base) =>
        @PV_RunJoin_NativeAttemptPublication55.actual (types base) (selected base heap box ops) {i with hash:=PV_RunJoin_CommonOracle51.hash W (toRP W Pr R h B outputs x w hN s).1})
      (fun i : @PV_RunJoin_NativeAttemptPublication55.Input (types base) =>
        @PV_RunJoin_NativeAttemptPublication55.published (types base) (selected base heap box ops) data plans {i with hash:=PV_RunJoin_CommonOracle51.hash W (toRP W Pr R h B outputs x w hN s).1}) := by
  letI : ExternalTypes := types base
  letI : ExternalFuns := selected base heap box ops
  have native := PV_RunJoin_NativeAttemptPublication55.complete base heap box ops data plans common backend finish query node ordering
  intro i
  exact native {i with hash:=PV_RunJoin_CommonOracle51.hash W (toRP W Pr R h B outputs x w hN s).1}
#print axioms complete
end R1Z.PV_RunJoin_NativeToRP55
