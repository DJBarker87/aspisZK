import PV_B3P_DependencyFinal559227
import PV_B3P_NextExtraction569227
namespace PV_B3P_Dependency569227
open Aeneas Aeneas.Std core.ops.range PV_B3P_Groups14227
set_option autoImplicit false
inductive Port where
  | previous (i : PV_B3P_ClosureFinal559227.Port)
  | default_next

def Signature (α : Type) : Port → Type
  | .previous i => PV_B3P_ClosureFinal559227.Signature α i
  | .default_next => Range Usize → Result (Option Usize × Range Usize)

def source (α : Type) : (i : Port) → Signature α i
  | .previous i => PV_B3P_ClosureFinal559227.source α i
  | .default_next =>
      PV_B3P_Std569Range227.core.ops.range.Range.Insts.CoreIterRangeRangeIteratorImpl.spec_next
        core.iter.range.StepUsize

def model (α : Type) : (i : Port) → Signature α i
  | .previous i => PV_B3P_ClosureFinal559227.model α i
  | .default_next => PV_B3Q_RangeActual.model

/-- Partial source-control catalogue extended by the directly emitted default
next. Its deployed specialization and caller application remain separate. -/
theorem partial_closure (α : Type) :
    PV_B3P_Link_std_dependency_closure14 (Signature α) (source α) (model α) := by
  intro i
  cases i with
  | previous i => exact PV_B3P_ClosureFinal559227.partial_closure559 α i
  | default_next => exact funext PV_B3P_NextExtraction569227.extraction_model_binding
#print axioms partial_closure
end PV_B3P_Dependency569227
