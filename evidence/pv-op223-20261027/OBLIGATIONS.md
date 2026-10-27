# Applied candidate proof and adoption obligations

The new implementation is confined to three files in aspis-r1-cost-probe.
The shared verifier compressor is retained byte-for-byte. APPLIED.json pins
the implementation revision and feature matrix; source-identity.json checks
the transported host sources against this worktree. Final-matrix extraction
must additionally confirm the initial generated declarations are unchanged.

Proved exact source law: R1Z.PV_Op223_Source.op223_source, installing only
the actual applied extraction as callback 223. The dependent P6 equation is
R1Z.PV_Op223_Source.P_source_p6. Both equations retain complete Result,
arbitrary tag, slice and lambda, all raw limbs, errors and divergence.

V164 BEFORE (exact immutable snapshot in ../pv-cb-20261026/RESUME5-V164-BEFORE.json):
ProverRw19CanonicalAuditRefinement.refinement takes P_source_p6, the durable
reservation equation, and P_proof_bytes. It quantifies over an arbitrary
ExternalFuns dictionary and carries the rest of that dictionary's obligations.

Candidate AFTER (PV_Op223_V164.refinement, Env-J43382 exit0): the same consumer
is specialized to PV_Op223_Source.selected ops, which installs the extracted
candidate compressor in op223. P_source_p6 is supplied by the proved exact
source/P6 equation. P_proof_bytes and the reservation equation remain explicit.
No raw input restriction, Result weakening, new trust item, protocol argument,
or replacement of the privacy endpoint is introduced. The generic historical
consumer remains unchanged for arbitrary dictionaries.

The source/P6/V164 theorems have passed focused compiles with standard axioms;
the final frozen audit remains scheduled after the native adoption gates. Adoption requires three rebuilt ELF pins, pinned fixtures, 1,000
fresh whole-prover pairs (coins 2000–2999), and lead-only quiet timing under
TIMING-PLAN.md. Timing is not run by this worker. No change to the capped
three-field trust list T is proposed. E1/E2, real RunJoin, proof bytes, the
OS-failure independence result, L1/L2/L3, and final coherent endpoint replay
remain deployment/proof obligations. Target not yet established.
