# L181: actual attempted events to the model law

`NGP_L181.lean` states NativeAssociation, Prefix_statement, Exact_statement
and their universally quantified L181_statement. Observation contains the
full Result and SdkC_Source.Log, whose Query carries parts and returned Result.
NativeAssociation must be proved from a physical run; instantiating it with a
source evaluation by definition is no native bridge. Prefix preserves the
failing syscall address; Exact additionally preserves successful replies and
terminal Result. `NGP_OracleTransport` proves these two substeps from native
association, P1/RuntimeSyscall, or ReturnsOnly+Agrees. It proves neither actual
association nor probability transfer for an arbitrary supplied observation.

| Boundary / difference | Exact needed lemma | Existing evidence / remaining gap |
|---|---|---|
| Physical syscall vs abstract digest | actual parts slices in order, returned reply unchanged, attempted query logged before interpreting reply | Native digest bridge NGC (op43; error op44), RuntimeSyscall.returningValue and P1 value trust. No SHA unrolling; all callers still need composition |
| Per-query iteration | Native log/state/results on arbitrary valid prestate, same Prepared/gamma/scratch/geometry | NFS_QueryLoopRoot.tx1/tx2 CLOSED under ae: fuels10/12, starts0/10, domains NFS_QueryInvariant.Domain and canonical scratch. These statements are RESULT equalities, not a full experiment log theorem |
| Transcript challenge generation | SAME Transcript::queries squeeze/digit stream; real rejection sampler, repeated indices and consumption order | TX1:168 OPEN; NFS uses the already supplied 22 indices and does not produce them. Sampler-first frozen3 order must be related to actual prepare/transcript calls |
| Duplicates in oracle queries | chronological occurrence-list equality; duplicate addresses remain in issued length, only first-read accounting dedups | ARW_Induced.issued/queries, RPx_Duplicates.repeated. No sorting/dedup of physical events is licensed |
| Repeated sampled indices | preserve all22 positions and their effects; multiproof index grouping may dedup node needs, not challenge issuance | Caller/native transcript and batch/preparation packets needed. A list of unique indices is not the sampled sequence |
| Pure verifier rejection | retain every event before the exact rejecting branch; no suffix events | ARS_QueryTransport.exact permits pure rejection when ReturnsOnly; RPx_Rejected.adaptive supplies model account rejection; driver association OPEN |
| Failed/diverging syscall | retain unsuccessful call's address; ideal continuation is a suffix, NOT a native call | RPx_AttemptPrefix.transport; PrefixBound (first1018, second903). RuntimeSyscall is successful-return only. Prefix does NOT establish equality of reply logs or a probability inequality by itself |
| Source vs frozen3 schedule | accepted raw canonical join OR already charged collision; preserve adaptive dependency of rearranged sampling/verification | ARX_Join.accepted model proof / F3S_Join.accepted_log_eq; native producer and event association remain. No new commuting rule for adaptive calls |
| Account replay / audit suffix | extra replay calls stay issued occurrences; same first-read support only where proved | RPx_Transport.Claims: prefix decomposition, exact firstReads, attempted bound Q+1921; replay/audit adds1044 first reads, total Q+2965. Not a claim that extra calls never occurred |
| Adversary between TXs | second phase reached only after actual first success; both reached logs charged with duplicates | ARW_Induced.program/issued/evaluation/queries; Q=Q0+Q1, L154 is parameter |
| Physical experiment mass | SAME submitted stored/public carrier, accepted failure event/extractor and unchanged ROM weights | ARX_Domination.pointwise → ARX_Mass.bounded → ARX_Residual.numeric. Admitted runtime zero extension outside game; no conditioning on success |

No inventory claims that NFS reorders or dedups digest events. It proves
loop/result laws. Known intentional model changes are sampler-first schedule,
canonical replays and omitted ideal suffixes after failed syscalls. Any OTHER
physical reorder found by the native event exporter must be recorded as a new
exact mismatch, never excused by acceptance equivalence. The table is a complete
map of current identified boundaries; the concrete native log exporter for the
OPEN drivers is required to prove absence of further differences.

Consumed CLOSED packets: NFS query roots, NFN for_range, S codec/scanner/emit,
NGC digest forwarding and other D helpers on their domains. OPEN: TX1:168;
prepare/Prepared/native driver association (including rejected prefixes);
checkpoint TX1:186; Pool B/D if the experiment includes the settlement consumer;
source-to-ELF trace realization. Prefix completion for terminal syscalls is a
proof obligation against the existing partial model, not an adopted totality
assumption. Candidate rows and owner choices are separated in PLAN/CANDIDATE_ROWS.
`Mass_statement` is the exact existing numerical target, not proved here for a
new physical runtime; the original per-attempt bound and collision accounting
are unchanged.

The full model-experiment statements, with every quantified dictionary,
adversary/support/owner/word/query hypothesis, are recorded by their complete current source signatures in
NGP_CONSUMER_SIGNATURES.txt (source hashes in NGP_INPUT_PINS.json): ARX_Join.accepted (raw/recovered OR collision),
ARX_Domination.pointwise (physical-view failure mass ≤ model failure mass +
indicator of that SAME recorder collision), ARX_Mass.bounded (lazyMean model
mass plus F3T_Numeric.accountLoss Q) and ARX_Residual.numeric. These statements
are the exact consumers of the per-code transport interface. The future
physical-instance job must construct their SAME ARU_Support.At/NativeAssociation
and bind ART_PhysicalView to the real observation; their already-proved model
instances are not re-proved or counted as physical closure here.

Loaded-name correction (L011): RPx_NativeTransport.PrefixBound,
RPx_Transport.Claims and RPx_Duplicates.repeated are historical source
interfaces NOT present in this combined import. Their exact historical
statements explain accounting/prefix shapes above but are NOT current loaded
certificate credit. The current checked sublemmas use RPx_AttemptPrefix and
ARS_QueryTransport; the headline's current experiment consumers are ARX/ARW.
This absence is retained as a finding, not repaired by importing old forests.
