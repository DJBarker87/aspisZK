import PV_B3P_ClosureLinks14227
set_option pp.fullNames true in
#print Aeneas.Std.core.fmt.num.imp.DisplayUsize.fmt
#print axioms Aeneas.Std.core.fmt.num.imp.DisplayUsize.fmt
#print Aeneas.Std.core.fmt.Formatter
#print axioms Aeneas.Std.core.fmt.Formatter
open Lean Elab Command
run_cmd do
 let name := Name.str (Name.str (Name.str .anonymous "core") "fmt") "Formatter"
 logInfo m!"unqualified core.fmt.Formatter is present: {((← getEnv).find? name).isSome}"
