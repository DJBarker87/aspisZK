import Uni_Accepted
import Uni_CanonicalPerAttempt
import Uni_SecondMarks
import Uni_RejectedSecond
import Uni_Slots
import Tx1Q_Accepted
set_option autoImplicit false
set_option pp.all false
set_option format.width 140
noncomputable section
namespace AspisR1.Uni_Audit
open Aeneas Aeneas.Std Result

/-- Consistency of the extraction boundary on the exact union. Native bodies
are identified with these owned bodies, not asserted to be deployed binaries. -/
theorem extraction_satisfiable {C F : Type} (adapter : AdapterRw.Ops)
    (ops : AspisR1CurrentCaller.Ops) (reserved : Bool) (query : Port3_NativeQueryBody.Ops)
    (geo : Port3_NativeGeometryBody.Ops C) (stage : VTop_Stages.Ops)
    (finish : AspisR1Stage2.Stage2Finish.FinishOps F)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries) (std : ClaimsUnrolledFinish.StdCalls)
    (hashv : S2Z.Oracle.Parts → Result S2Z.Oracle.Digest) :
    ∃ native1 native2, S2W_DigestExtraction.AeneasExtraction
      (ClaimsUnrolledSdk.sdkOps
        (Tx2I_Install.install {adapter with op43 := S2W_DigestExtraction.digest hashv}
          (Op5T_Concrete.stage stage) finish)
        (Uni_Install.current ops reserved query geo) B std) native1 native2 hashv := by
  let actual := ClaimsUnrolledSdk.sdkOps
    (Tx2I_Install.install {adapter with op43 := S2W_DigestExtraction.digest hashv}
      (Op5T_Concrete.stage stage) finish) (Uni_Install.current ops reserved query geo) B std
  exact ⟨AdapterRw.r1_pool_adapter.owned.stage1_owned actual,
    AdapterRw.r1_pool_adapter.owned.stage2_owned actual,⟨by intros; rfl,by intros; rfl,by intros; rfl⟩⟩

#check @Op4P_Accepted.accepted_pair_claims_op34
#check @Tx2I_Accepted.accepted_pair_claims_tx2
#check @Op5T_Final.accepted_pair_claims_op5
#check @Tx1Q_Accepted.accepted_pair_claims_tx1
#check @Uni_Accepted.accepted_pair_unified
#check @OraclePortHeadlineFrozen2PerAttempt.final_soundness
#check @Uni_CanonicalPerAttempt.final_soundness
#print S2W_TraceSplice.FirstMarks
#print S2W_TraceSplice.SecondMarks
#print Op5T_Marks.FirstMarks
#print Op5T_Marks.SecondMarks
#print Op5T_Marks.accepted
#print Tx1Q_Endpoint.WhenBound
#print Port1_CanonicalJoin.AcceptedVerifierJoin
#print Port1_CanonicalJoin.AcceptedRunJoin
#print Uni_Install.base
#print Uni_Install.current

#print axioms Uni_Install.compose_tx1
#print axioms Uni_Install.scan_batch
#print axioms Uni_Install.prefix_batch
#print axioms Uni_Install.overlap
#print axioms Uni_Cuts.tx1
#print axioms Uni_Cuts.scan
#print axioms Uni_Accepted.accepted_pair_unified
#print axioms Uni_SecondMarks.authenticated_order
#print axioms Uni_SecondMarks.accepted_source_marks
#print axioms Uni_SecondMarks.successful_fixture
#print axioms Uni_RejectedSecond.shape_rejects
#print axioms Uni_RejectedSecond.rejected_source
#print axioms Uni_RejectedSecond.second_marks_force_resume
#print axioms Uni_RejectedSecond.no_global_second_mark_association
#print axioms Uni_CanonicalPerAttempt.final_soundness
#print axioms Uni_CanonicalPerAttempt.no_global_join
#print axioms Uni_CanonicalPerAttempt.failure_bound
#print axioms Uni_Slots.stage_commutes
#print axioms Uni_Slots.current_slots
#print axioms Uni_Slots.stage_slots
#print axioms extraction_satisfiable
end AspisR1.Uni_Audit
end
