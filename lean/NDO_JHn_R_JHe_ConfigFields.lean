import NDO_JHe_Configuration
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHe_ConfigFields
open Aeneas Aeneas.Std Result DrvC_Installation
abbrev config := JHe_Configuration.value

theorem base (a : AdapterRw.Ops) (s : VTop_Stages.Ops) : (config a s).currentBase=JGp_Allocation.base JGp_Seeds.base := rfl
#print axioms base
theorem reserved (a : AdapterRw.Ops) (s : VTop_Stages.Ops) : (config a s).reserved=true := rfl
#print axioms reserved
theorem query (a : AdapterRw.Ops) (s : VTop_Stages.Ops) : (config a s).query=SAQ_Decoder.install (JFr_TX2_DotsBinding.ops JGp_Seeds.query) := by
  rfl
#print axioms query
theorem geometry (a : AdapterRw.Ops) (s : VTop_Stages.Ops) : (config a s).geometry=SAQ_Constructor.install () JGp_Seeds.geometry := rfl
#print axioms geometry
theorem boundaries (a : AdapterRw.Ops) (s : VTop_Stages.Ops) : (config a s).boundaries=JGe_Boundaries.value := rfl
#print axioms boundaries
theorem std (a : AdapterRw.Ops) (s : VTop_Stages.Ops) : (config a s).std=NP6_StdModel.calls (.Ok ()) := rfl
#print axioms std
end AspisR1.JHe_ConfigFields
end
