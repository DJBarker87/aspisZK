import NDO_JHn_R_JHe_CurrentShape
import NDO_JHn_R_JHe_WriterCommutation
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHe_CurrentAssociation
open Aeneas Aeneas.Std Result AspisR1CurrentCaller

theorem allocation (base : Ops) :
    Op5T_Concrete.current (JGp_Allocation.base base)=JGp_Allocation.base (Op5T_Concrete.current base) := by
  cases base
  rfl
#print axioms allocation

/-- Exact content dictionary association; the selector writer remains a
separate same-run bridge, not an unproved whole-dictionary equality. -/
theorem source (adapter : AdapterRw.Ops) (stage : VTop_Stages.Ops) :
    JHe_Configuration.contentCurrent adapter stage=JGr_Geometry.installed := by
  unfold JHe_Configuration.contentCurrent
  rw [JHe_CurrentShape.source,allocation,←JHe_WriterCommutation.actual]
  rfl
#print axioms source
end AspisR1.JHe_CurrentAssociation
end
