# Stage 3: exact TX2 source program

DrvC_SecondProgram.program proves literal Program equality between the
constructed interpreter's authenticated TX2 and GExp_Experiment.second on
DrvC_Installation.stage/digest. This is an all-outcome statement: same ordered
reads, duplicates, rejection prefixes and complete Result. No accepted-run
compatibility hypothesis or oracle realization is needed for the program
identity. DrvC_SecondCode.common and DrvC_AuthenticatedCode.code establish the
literal source syntax equality, using the phantom batch-dictionary lemma.
DrvC_Flow.tx1 and DrvC_SecondFlow establish both whole typed tree lowerings.

The first-stage bridge is not yet complete. DrvC_CurrentSlots.current_base
identifies its exact source dictionary; DrvC_FirstBatch.batch already proves
its batch source Code equality under nominal error transport, without a
selected-map or successful-call premise. DrvC_MapCode and DrvC_OraclePort
provide ordered-effect-preserving carrier transport laws.

L160 remains OPEN; no ledger premise removed yet. No retained source,
cryptographic, runtime, trust or other-cone hypothesis changed.

Attempts through 033: all exact receipts retained. 023 hit deterministic
200000-heartbeat timeout at whnf (exit 1,16.8717s,5569252KiB,swap0). It was
NOT retried unchanged. Its proof was split into AuthenticatedCode (030) and
SecondProgram (032), and the checked common theorem was made opaque locally.
Both replacements pass in about 2 seconds. No cap/heartbeat raise. Other
failures are excluded development elaboration goals, retained in full.
006 is the documented no-compiler dependency preflight failure. No Kani,
Rust/SBF, package replay, shipped-file change or key operation.

Each passing new theorem has a printed standard-only axiom audit. Receipts
record target, source revision+SHA, deps fingerprint, exit,wall,RSS,swap,caps.
Next deliverable: finish TX1 carrier/Program transport, join it to the native
accepted pair and headline, and establish concrete successful-fixture acceptance.
