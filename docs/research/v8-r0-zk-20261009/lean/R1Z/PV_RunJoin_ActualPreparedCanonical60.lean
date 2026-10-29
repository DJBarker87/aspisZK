import R1Z.PV_RunJoin_ActualRun59
import R1Z.PV_RunJoin_PrepareScalarFields49
import R1Z.PV_RunJoin_ScalarRaw50
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_ActualPreparedCanonical60
open Aeneas Aeneas.Std Result ProverRwFull PV_RunJoin_WeightInstalled46
open ProverCommitWideOps48

theorem complete (base : ExternalTypes) (heap : Heap) (box : Box)
    (ops : @ExternalFuns (types base)) :
    letI : ExternalTypes := types base
    letI : ExternalFuns := selected base heap box ops
    ∀ (phase : PV_RunJoin_NativeControl55.Phase) (prepared : prover.PreparedOpening),
    prover.prepare_opening .S2 phase.hash phase.backend phase.sem=ok (.Ok prepared) →
    canonical (PV_RunJoin_ActualRun.data phase).g ∧
    canonical (PV_RunJoin_ActualRun.data phase).k ∧
    canonical (PV_RunJoin_ActualRun.data phase).a := by
  letI : ExternalTypes := types base
  letI : ExternalFuns := selected base heap box ops
  intro phase prepared success
  obtain ⟨g,k,a,hg,hk,ha,eg,ek,ea⟩ := PV_RunJoin_PrepareScalarFields49.complete
    base heap box ops .S2 phase.hash phase.backend phase.sem prepared success
  have roundtrip (x : Raw) : PV_RunJoin_ActualData59.rawW (ProverRwDictionaryTower.fromW (source x))=x :=
    PV_RunJoin_ScalarRaw50.roundtrip x
  simp only [PV_RunJoin_ActualRun.data,PV_RunJoin_ActualData59.data,
    PV_RunJoin_ActualData59.preparedField,PV_RunJoin_ActualRunSources59.prepare,success,
    eg,ek,ea,roundtrip]
  exact ⟨hg,hk,ha⟩

#print axioms complete
end R1Z.PV_RunJoin_ActualPreparedCanonical60
