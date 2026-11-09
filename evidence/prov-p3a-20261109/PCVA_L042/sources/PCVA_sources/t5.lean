import Aeneas
open Aeneas Aeneas.Std Result ControlFlow
set_option pp.proofs false
#print Aeneas.Std.instPartialOrderResult
#print Aeneas.Std.Result.le
#check @Aeneas.Std.Result.admissible_eq_or_div
open Lean.Order in
#check @admissible_pi
#check @Lean.Order.admissible_pi_apply
#check @Lean.Order.PartialOrder.rel_antisymm
#check @Lean.Order.monotone_bind
#check @Aeneas.Std.loop.fixpoint_induct
