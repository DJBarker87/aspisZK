import R1Z.PV_Src_PublicInstalledRoot
import R1Z.PV_Src_NativeRootReduced
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_Src_NativeInstalledRootReduced
open Aeneas Aeneas.Std Result R0Z.WriterRefine
open BuilderForestAdmissionPort PV_Src_NativeInput
variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K] [CharP K 2147483647]

theorem source {I : Type} (external : ExternalLinear) (records : Records)
    (inputs : I → Input) (transport : Fin 1024 ≃ Fin 1024)
    (external_law : PV_Src_ExternalAssociation.Associated external)
    (records_law : PV_Src_RecordAssociation.Associated external records)
    (frontier : ∀ i (l : Fin 20), Canon8 (inputs i).snapshot.frontier.val[l.val]!)
    (core : PV_Src_NativeRootReduced.Core (K := K) external records inputs transport) :
    @PV_Src_NativeIdentification.PV_Src_Premises K _ _ external records I inputs transport where
  compile_call := core.compile_call
  words := core.words
  publicCorr := fun i r hr => PV_Src_PublicInstalledRoot.correspondence external records
    external_law records_law (inputs i) (core.compile_call i) (frontier i) r hr
  admission := core.admission
  row_call := core.row_call

#print axioms source
end R1Z.PV_Src_NativeInstalledRootReduced
