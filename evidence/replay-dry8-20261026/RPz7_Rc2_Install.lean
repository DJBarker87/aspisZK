import RPz7_T2R_Top
import RPz7_NP6_StdModel
set_option autoImplicit false
noncomputable section
namespace AspisR1.Rc2_Install
/-- Select the checked NP6 source instance, preserving every other input slot.
The original free std slot is deliberately replaced, not assumed compatible. -/
def select {F C : Type} (c : DrvC_Installation.Configuration F C)
    (reservation : NP6_StdModel.Reservation) : DrvC_Installation.Configuration F C :=
  {c with std := NP6_StdModel.calls reservation}

def configuration {F C : Type} (c : DrvC_Installation.Configuration F C)
    (reservation : NP6_StdModel.Reservation) :=
  DrvC_FirstConstants.configuration (select c reservation)

theorem standard {F C : Type} (c : DrvC_Installation.Configuration F C)
    (reservation : NP6_StdModel.Reservation) :
    (configuration c reservation).std = NP6_StdModel.calls reservation := rfl

theorem dictionary {F C : Type} (c : DrvC_Installation.Configuration F C)
    (reservation : NP6_StdModel.Reservation) :
    DrvC_Installation.sdk (configuration c reservation) =
      SdkD_PairBatches.dictionary (configuration c reservation).adapter
        (configuration c reservation).currentBase (configuration c reservation).stageBase
        (configuration c reservation).finish (configuration c reservation).reserved
        (configuration c reservation).query (configuration c reservation).geometry
        (configuration c reservation).boundaries (NP6_StdModel.calls reservation) :=
  DrvC_Installation.aus1_dictionary (configuration c reservation)

#print axioms standard
#print axioms dictionary
end AspisR1.Rc2_Install
end
