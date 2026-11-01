# Ruling (y) frame audit (in progress)

The validator has six immediate conservative internal edges: common getter,
public tuple projection, two payment encoders, output-lane helper, late encoder.
NED_K034/K035 are retained as the binding ruling's caller-control input;
NED's independent call-window/field-binding pairs retain exact argument facts.
NEE_K002/K003/K004 are excluded timeouts of attempted combined extensions,
not invalidations of that inherited evidence. No timeout shape is retried.

Part (2) additionally requests an exact modifies contract. The selected NBP
payment native harnesses (K031..034) execute the actual functions directly,
without proof_for_contract/modifies attributes. Their result-byte laws and
model proofs remain valid local evidence; their missing explicit contract
frame is retained as a finding, not converted into root PhysicalInterpretation.

First new frame target: M31::to_le_bytes (the genuine scalar serializer;
WideExact::to_le_bytes is a conservative alternative, not the receiver here).
Only cfg(kani) contract attributes are applied in the private frozen scratch
copy; source erasure is checked byte-for-byte against 4bb3b3f5. The actual
body and all deployed features remain unchanged. Inverted postconditions
are negative controls, not alternate implementation proofs.
