import LIB_VCarriers
import Lean
set_option autoImplicit false
set_option pp.all true
open Lean Elab Command
namespace NNI_CollectorAcc

/-- Diagnostic type alias only; this is not a native packet or row owner. -/
abbrev Alias : Type := LIB_VCarriers.Acc

theorem alias_identity : Alias = LIB_VCarriers.Acc := rfl
#print LIB_VCarriers.Acc
#print axioms LIB_VCarriers.Acc
#print axioms alias_identity

run_cmd do
  let env := (← getEnv).setExporting false
  let root := `NNI_CollectorAcc.alias_identity
  let some c := env.find? root | throwError "missing diagnostic root"
  let statement ← liftTermElabM (PrettyPrinter.ppExpr c.type)
  let row := Json.mkObj [("root",toJson root.toString),
    ("owner_module",toJson "NNI_CollectorAcc"),
    ("obligation_statement",toJson statement.pretty)]
  logInfo m!"NNI_OWNER {row.compress}"
end NNI_CollectorAcc
