import R1Z.PV_CB3_Op120Source
import R1Z.PV_CB3_Op225Source
import R1Z.PV_CB3_Op246Source
import R1Z.PV_CB3_Op51Arbitrary
set_option pp.explicit true
#print R1Z.PV_CB3_Op120Source.Raw.BoundaryAcc
#check @R1Z.PV_CB3_Op120Source.op120_source
#print axioms R1Z.PV_CB3_Op120Source.op120_source
#check @R1Z.PV_CB3_Op225Source.op225_source
#print axioms R1Z.PV_CB3_Op225Source.op225_source
#check @R1Z.PV_CB3_Op225Source.adapters_independent
#print axioms R1Z.PV_CB3_Op225Source.adapters_independent
#check @R1Z.PV_CB3_Op246Source.op246_source
#print axioms R1Z.PV_CB3_Op246Source.op246_source
#check @R1Z.PV_CB3_Op51Arbitrary.carrier_complete
#print axioms R1Z.PV_CB3_Op51Arbitrary.carrier_complete
#check @R1Z.PV_CB3_Op51Arbitrary.op51_source
#print axioms R1Z.PV_CB3_Op51Arbitrary.op51_source
