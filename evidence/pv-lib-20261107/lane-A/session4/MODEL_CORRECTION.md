# D981 correction applied by Lane A

Before: writer graph at PV_THR2_SourceStoreInterpreter.step, whose neutral
branch is PV_THR2_IntrinsicState.step.
After: PV_LIB_A_OwnerStore.step, whose neutral branch is
PV_THR2_OwnInitInterpreterBridged.step. Writer meanings are literally
PV_THR2_SourceStoreLibrary.interpret, with its existing Values record.

Reason: LOG D981/SPEC-C2 identifies the missing OWNER registration at actual
f361/storage-live14320. No old module is edited. Away agreement is against the
OWNER-aware interpreter. Existing failed/pending/aborting/diverging replies,
world/event effects, source-store malformed-layout undefined arm and suspended
stack are retained. Values, reference provenance and caller histories are not
replaced by a source-write premise or an identity effect.

This corrects the machine toward source execution. It changes no endpoint
security content, trust field, implementation, row consumer or ledger status.
