import Aeneas
import EbyKPushExplicitTypesV1

open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false

namespace AspisR1FastDotsCurrent

/-- Source-pinned aliases to the existing field and EbyK owners.  These replace
    Aeneas external type axioms; source-coordinate correspondence is recorded
    separately by the S4 type checker. -/
abbrev aspis_core.field.M31 := AspisR1EbyKPushCutV3.field.M31
abbrev aspis_core.field.CM31 := AspisR1EbyKPushCutV3.field.CM31
abbrev aspis_core.field.QM31 := AspisR1EbyKPushCutV3.field.QM31
abbrev aspis_core.field.wide_exact.WideExact :=
  AspisR1EbyKPushCutV3.field.wide_exact.WideExact
abbrev fast_pairing.EbyKDot := AspisR1EbyKPushCutV3.fast_pairing.EbyKDot

/-- Aeneas-generated closure representation, retained verbatim in shape. -/
def fast_dots.four_dots.closure :=
  Array Std.U8 608#usize × Array aspis_core.field.wide_exact.WideExact 29#usize

/-- Aeneas-generated reducer closure representation. -/
abbrev fast_dots.four_dots.closure.closure := Array Std.U64 8#usize

end AspisR1FastDotsCurrent
