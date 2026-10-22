import S4InstalledCurrentQmParserSourceV1
import S4FourCallbacksForwardRootV1
import S4V10LiteralHelperSourceCutV1

set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1FastDotsS4FinalInstalledQMToV10V1

open AspisR1FastDotsCurrentQmParserRootV1
open AspisR1FastDotsV10CarrierMapV1

abbrev Ops := AspisR1FastDotsCurrent.FourDotsOps
abbrev U8 := Aeneas.Std.U8
abbrev ActualQMParser := AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes

theorem final_install_parser_is_actual
    (base : Ops) (bytes : Slice U8) :
    (AspisR1FastDotsFourCallbacksForwardRootV1.install base).qm31FromBytes bytes =
      mapResult (Option.map toCurrent) (ActualQMParser bytes) := by
  change (AspisR1FastDotsConcreteTailInstallRootV1.install
      (AspisR1FastDotsFourCallbacksForwardRootV1.arrayOps base)).qm31FromBytes bytes = _
  exact AspisR1FastDotsInstalledCurrentQmParserSourceV1.installed_parser_is_actual_source
    (AspisR1FastDotsFourCallbacksForwardRootV1.arrayOps base) bytes

/-- The literal helper's QM parser slot, after the final four-callback Ops
installation, is exactly the transparent generated QM31 parser followed by
the accepted V10 carrier map. This is all-result, all-slice equality. -/
theorem literal_parser_is_actual_accepted_v10
    (base : Ops) (bytes : Slice U8) :
    AspisR1FastDotsV10LiteralHelperSourceCutV1.literalQMFromBytes
        (AspisR1FastDotsFourCallbacksForwardRootV1.install base) bytes =
      mapResult (Option.map (fun q => qm31ToEbyK (toCurrent q)))
        (ActualQMParser bytes) := by
  unfold AspisR1FastDotsV10LiteralHelperSourceCutV1.literalQMFromBytes
  rw [final_install_parser_is_actual]
  cases h : ActualQMParser bytes <;> simp [mapResult, h]

#print axioms final_install_parser_is_actual
#print axioms literal_parser_is_actual_accepted_v10

end AspisR1FastDotsS4FinalInstalledQMToV10V1
