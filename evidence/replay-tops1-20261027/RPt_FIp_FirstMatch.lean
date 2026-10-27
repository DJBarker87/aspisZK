import RPt_FIp_InstalledLaws
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIp_FirstMatch
open Aeneas Aeneas.Std Result DrvC_Installation
abbrev E := AspisR1Stage2.Stage2Finish.E

theorem selected {C : Type} (err : C) (c : Configuration FIo_Install.W C) (r : NP6_StdModel.Reservation)
    (alpha folded selected : E) (values : Array E 4#usize) (inverse : Array U32 5#usize)
    (fold : (FIp_Install.configuration err c r).query.op17 alpha values inverse=ok folded)
    (compared : core.cmp.PartialEq.ne.trait_default (FIp_Install.configuration err c r).query.widePartialEq
      folded selected=ok false) :
    CheckpointBytes5Output.ofE selected=FoldRuntimeAlgebra.circleWithInverses (CheckpointBytes5Output.ofE alpha)
      (algebraMap Port5Q1_QueryPorts.FP Port5Q1_QueryPorts.FE
        (S7JoinBasisMachine.decode (Port5Q1_GeometryBinding.lane inverse 0)))
      (algebraMap Port5Q1_QueryPorts.FP Port5Q1_QueryPorts.FE
        (S7JoinBasisMachine.decode (Port5Q1_GeometryBinding.lane inverse 1)))
      (Port5Q1_OpeningValues.values values) := by
  have same := FIp_InstalledLaws.compared err c r folded selected compared
  rw [←same]
  exact (FIp_CircleQuery.exact_circle alpha values inverse folded fold).1

#print axioms selected
end AspisR1.FIp_FirstMatch
end
