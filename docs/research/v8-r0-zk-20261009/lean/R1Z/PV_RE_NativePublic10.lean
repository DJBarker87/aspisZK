import R1Z.PV_RE_NativeAssociationsB10
import R1Z.PV_Src_PublicRootAssociation
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_NativePublic10
open Aeneas Aeneas.Std Result BuilderForestAdmissionPort
open BuilderForestAdmissionPort.pool_v1 PV_Src_NativeInput
local instance : CharP PV_Src_FrozenFixtures.Scalar 2147483647 :=
  charP_of_injective_algebraMap
    (algebraMap (ZMod AspisCircleGroupOrder.P) PV_Src_FrozenFixtures.Scalar).injective
    AspisCircleGroupOrder.P

def inputs (compiled : Bool → pair_forest_trace.PoolV1PairForestMergedC1CompilationV1)
    (anchor : Array U32 8#usize) (pool domain destination : PV_Src_PublicRecords.Context)
    (withdrawal : Bool) : Input :=
  PV_Src_FrozenInput.input (PV_Src_FrozenFixtures.data withdrawal (compiled withdrawal) anchor pool domain destination)

/-- Exact public association, conditional on the exact compiler-call law.
The compiler-call law remains a native P obligation, not an existence witness. -/
theorem association
    (compiled : Bool → pair_forest_trace.PoolV1PairForestMergedC1CompilationV1)
    (anchor : Array U32 8#usize) (pool domain destination : PV_Src_PublicRecords.Context)
    (compile_call : ∀ withdrawal,
      @run PV_Src_FrozenInput.external
        (@PV_Src_RecordDynamic.dictionary PV_Src_FrozenInput.external)
        (inputs compiled anchor pool domain destination withdrawal) =
      ok (.Ok (inputs compiled anchor pool domain destination withdrawal).compiled)) :
    PV_Src_PublicDeploymentAssociation.Association
      (@PV_Src_RecordDynamic.dictionary PV_Src_FrozenInput.external)
      (inputs compiled anchor pool domain destination) := by
  apply PV_Src_PublicRootAssociation.source _ compile_call
  intro withdrawal l
  exact PV_Src_FrozenInput.frontier _ l
#print axioms inputs
#print axioms association
end R1Z.PV_RE_NativePublic10
