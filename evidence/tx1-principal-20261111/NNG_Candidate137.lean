import NNG_SourceParse137
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_Candidate137

theorem candidate : RSL.TX1_137.RowSpec_137 LIB_VLib.library NNG_Producer137.producer := by
  intro a obs env domain
  rw [NNG_Producer137.tree]
  exact NNG_SourceParse137.source a obs env domain
#print axioms candidate
end AspisR1.NNG_Candidate137
