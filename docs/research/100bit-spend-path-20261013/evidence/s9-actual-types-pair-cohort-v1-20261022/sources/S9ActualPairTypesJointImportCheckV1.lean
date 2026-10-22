import S9ActualCoreFieldTypesV1
import AspisR1S9PairCallerStepV1.Types

set_option autoImplicit false
open Aeneas.Std

#synth Aeneas.Std.Discriminant
  AspisR1S9ActualFieldTypesCutV1.transport.Variant Aeneas.Std.Isize
#synth Aeneas.Std.Discriminant
  AspisR1S9PairCallerStepV1.transport.Variant Aeneas.Std.Isize

example :
    AspisR1S9ActualFieldTypesCutV1.transport.Variant.read_discriminant .S1 =
      0#isize := rfl

example :
    AspisR1S9PairCallerStepV1.transport.Variant.read_discriminant .S1 =
      0#isize := rfl
