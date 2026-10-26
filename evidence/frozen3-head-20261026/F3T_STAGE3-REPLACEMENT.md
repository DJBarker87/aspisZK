# Accepted canonical proof replacement

F3T_AcceptedReplacement.program proves full oracle Program equality between
an accepted F3 model input and the SAME input whose ghost proof is rebuilt
by Port1_StoredCarrier.proof from its stored bytes. No stored/log/semantic
replacement is hypothesized. F3T_AlignedRows derives the initial root and all
consumed payloads from parsed transcript alignment; F3T_ParsedRows derives
row bounds from actual parser success. F3T_PrefixCongr proves precisely the
33-row equality needed: F3's terminal message is ignored. Unused proof tails
are not a new restriction on source submissions. This repairs one canonical
input-association subproblem; the source semantic serialization and collision
cases remain separate.

F3T_InstalledRecovered now specializes decoded public/29initial/folded-final
agreement and per-coin extraction equality to the actual F3 installed source,
with the BYTE raw join explicitly retained. Generic all-input RawJoin is not
used for this specialization and is uninhabitable for an accepting physical
source, as064 proves.

Passing069/070/071/073AlignedRows,074/075PrefixCongr,078/079ParsedRows,
081AcceptedParser,082AcceptedReplacement,084/086InstalledRecovered,
085InitFrame.072/076/083 excluded elaboration diagnostics.077 was a premature
missing-own-dependency preflight, no compiler; no launcher repair or bypass.
080 passed while its direct dependency was being updated; conservatively
excluded from final provenance.081 recompiles against the NEW dependency
fingerprint and passes. This rerun is justified by changed dependency bytes,
not an unchanged regression. All accepted source snapshots use only standard
axioms and every theorem has printed audit output. Caps unchanged6G/8G/
Swap0/Tasks64,-M7000; no resource failure or package replay.

Through086:84actual Lean runs (027/077 no compiler),0Kani. Counts include all
excluded compiler diagnostics. No shipped edit,ELF rebuild or key operation.
