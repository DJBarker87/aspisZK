import Aeneas
open Aeneas Aeneas.Std Result ControlFlow
set_option pp.proofs false
#print Aeneas.Std.loop
#check @Aeneas.Std.loop.fixpoint_induct
#check @Aeneas.Std.loop.eq_1
#print Aeneas.Std.Result.bind
#check @Aeneas.Std.loop_eq
