import NFY_Part060
set_option autoImplicit false
run_cmd do
 let env ← Lean.getEnv
 let some c := env.find? `AspisR20Request.pool_v1.pair_forest_terminal.decode_pool_v1_pair_forest_terminal_request_reference_v1 | throwError "missing reference"
 for n in (c.value? true).get!.getUsedConstants do
  if n.toString.contains "PartialEq" || n.toString.contains "transition_kind" then
   Lean.logInfo m!"{n}"
#print AspisR20Request.Slice.Insts.CoreCmpPartialEqSlice
#print Aeneas.Std.core.slice.cmp.PartialEqSlice.eq
#print AspisS6StdByteSlice.eq_exact
#print AspisR20Request.pool_v1.payment_relation.POOL_V1_PAYMENT_STATEMENT_BYTES
