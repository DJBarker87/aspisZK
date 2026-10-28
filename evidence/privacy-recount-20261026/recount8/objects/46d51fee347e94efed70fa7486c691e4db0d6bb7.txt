import R1Z.PV_Ext_DiagnosticOp36Types
open Aeneas Aeneas.Std Result ControlFlow Error
namespace PV_Ext_DiagnosticOp36
class ExternalFuns where
  op0 : Result aspis_core.field.QM31
abbrev aspis_core.field.QM31.ZERO [ext : ExternalFuns] := @ExternalFuns.op0 ext
end PV_Ext_DiagnosticOp36
