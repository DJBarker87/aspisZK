import R1Z.ProverRw18AxiomsAudit
set_option autoImplicit false

-- One cached component manifest. Source cuts and whole-model data equations
-- remain visible in the printed consumer types. No deployed-release claim.
#check R1Z.ProverRw18ContextJoin.callback
#check R1Z.ProverRw18ContextDataIff.criterion
#check R1Z.ProverRw18ComponentGate.gate
#check R1Z.ProverRw18FixtureDecode.transfer
#check R1Z.ProverRw18FixtureDecode.withdrawal
#print axioms R1Z.ProverRw18ContextJoin.callback
#print axioms R1Z.ProverRw18ContextDataIff.criterion
#print axioms R1Z.ProverRw18ComponentGate.gate
#print axioms R1Z.ProverRw18FixtureDecode.transfer
#print axioms R1Z.ProverRw18FixtureDecode.withdrawal
