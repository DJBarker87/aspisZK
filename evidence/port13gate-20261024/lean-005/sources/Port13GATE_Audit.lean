import Port13GATE_Authenticated
import Port11PROV_Authenticated

-- Printer settings only; no elaborator heartbeat or recursion limit changes.
set_option pp.deepTerms true
set_option pp.maxSteps 100000
set_option pp.fullNames true
set_option pp.universes true

-- Complete before/after theorem types, including identical actual-source witnesses.
#check @AspisR1.Port11PROV_Authenticated.accepted
#check @AspisR1.Port13GATE_Authenticated.accepted

-- Expand every gate and the proof-only witness; no output equality is hidden
-- in a newly introduced input structure.
#print AspisR1.MultiproofConeP6Frozen2Stage.P6Boundary
#print AspisR1.MultiproofConeP6Callbacks.ParentGate
#print AspisR1.MultiproofConeP6Batch.LeafGate
#print AspisR1.LiteralByteProtocol.Decoder
#print AspisR1.Port1_StoredCarrier.ByteProver
#print AdapterRw.Ops
#print VTop_Stages.Ops
#print AspisR1.Port1_Library.TrustedStd
#print AspisR1.Port13GATE_Canonical.dictionary
#print AspisR1.Port13GATE_Canonical.boundary
#check @AspisR1.Port13GATE_Canonical.both_batches
#print AspisR1.MultiproofConeP6Frozen2Stage.sourceBatch
#print AspisR1.OraclePortFrozen2.batch
#print AspisR1.Port9OR_Code.native
#print AspisR1.Port9OR_Code.program
#check @AspisR1.Port9OR_Code.oracle
#check @AspisR1.Port10AUTH_Installed.accepted

#print axioms AspisR1.Port13GATE_Canonical.boundary
#print axioms AspisR1.Port13GATE_Canonical.both_batches
#print axioms AspisR1.Port13GATE_Authenticated.accepted
#print axioms AspisR1.Port11PROV_Authenticated.accepted
#print axioms AspisR1.Port10AUTH_Installed.accepted
#print axioms AspisR1.Port11PROV_FirstBoth.accepted
#print axioms AspisR1.Port6AUTH_Recovery.batches
