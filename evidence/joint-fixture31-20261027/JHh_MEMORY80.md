# Attempt080: six-level continuation split

Tree1C_A (six remaining levels) hit -M7000, exit134,wall165.048347197s,
RSS7170000KiB,swap0,interpreter memory_exception. No credit assigned.
Replacement splits levels06-08 from09-11, exactly the checked tree0 shape.
Tree2 is split proactively the same way; no unchanged failed source rerun.

Two small sequential proof groups preserve budget: PreBatch+BatchFrontier
are checked in JHh_PreBatchAssembly, and Child+TX1+ActualWitness in
JHh_TX1Assembly. Their declaration bodies and names are retained, external
imports unioned, only internal self imports removed. Every theorem has its
#print axioms. These groups do not import unconditional tree realizations
or the headline. No module-system/private-body mechanism or cap change.
