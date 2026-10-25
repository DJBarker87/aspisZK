import Port16CUT_Accounting
set_option autoImplicit false
set_option pp.all true
set_option pp.proofs false
open AspisR1
#check @Port16CUT_TX2.tx2
#check @Port15DRIVER_TX1.tx1
#check @Port16CUT_Cuts.sourceOne_eq
#check @Port16CUT_Cuts.sourceTwo_eq
#check @Port16CUT_Cuts.sourceOne_bound
#check @Port16CUT_Cuts.sourceTwo_bound
#check @Port16CUT_Driver.stages_eq
#check @Port16CUT_Driver.next_bound
#check @Port16CUT_Driver.stages
#check @Port16CUT_Driver.rust
#check @Port16CUT_Driver.rust1161
#check @Port16CUT_Accounting.budget
#check @Port16CUT_Accounting.log_length
#check @Port1_StoredCarrier.driver_physical
#check @Port6AUTH_Accounting.budget
#check @Port6AUTH_Accounting.log_length
#print Port15DRIVER_Local.LocalBudgets
#print Port15DRIVER_Local.delegatedIds
#print Port16CUT_Cuts.sourceOne
#print Port16CUT_Cuts.sourceTwo
#print Port16CUT_Cuts.oneWeight
#print Port16CUT_Cuts.twoWeight
#print Port16CUT_Cuts.delegatedWeight
#print Port15DRIVER_TX1.sites
#print Port16CUT_TX2.sites
#print Port16CUT_Driver.next
#print Port1_Driver.stages
#print Port1_Driver.rust
#print Port1_StoredCarrier.Physical
#print axioms Port16CUT_TX2.tx2
#print axioms Port15DRIVER_TX1.tx1
#print axioms Port16CUT_Cuts.sourceOne_eq
#print axioms Port16CUT_Cuts.sourceTwo_eq
#print axioms Port16CUT_Cuts.sourceOne_bound
#print axioms Port16CUT_Cuts.sourceTwo_bound
#print axioms Port16CUT_Driver.stages_eq
#print axioms Port16CUT_Driver.next_bound
#print axioms Port16CUT_Driver.stages
#print axioms Port16CUT_Driver.rust
#print axioms Port16CUT_Driver.rust1161
#print axioms Port16CUT_Accounting.budget
#print axioms Port16CUT_Accounting.log_length
#print axioms Port1_StoredCarrier.driver_physical
#print axioms Port6AUTH_Accounting.budget
#print axioms Port6AUTH_Accounting.log_length
#print axioms Port16CUT_Bind.done_tail_length
#print axioms Port16CUT_Cuts.one_sum
#print axioms Port16CUT_Cuts.two_sum
#print axioms Port16CUT_Cuts.weights
