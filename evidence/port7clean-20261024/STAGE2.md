# Native terminal composition and exact remaining obstruction

## Before / after, with assumption accounting

Before: Port6AUTH_Query.accepted concludes saved-ten/twelve/completeState,
weight lengths/counters, all recovered-map identity and two-pass word stability.
It does not conclude terminal Checks. Port4D_FinishFrozen.accepted_finish assumes
an independently supplied completeState equation and concludes frozen finish.
Port6AUTH_Headline.final_soundness assumes the full source CleanAcceptedModel.

After: `Port7CLEAN_Accepted.terminal_from_calls` concludes

```
Nonempty (LiteralAcceptanceTerminal.Checks run.2.1.1
  ((LiteralByteProtocol.protocol decoder).transcript H run.2.1.1
    (RawCutTranscriptRun.proof
      (RawCutWordsFromRunExecutableBin.wordsFromRun run) run.2.1.2) 33).rounds)
where run = eval H (Port6AUTH_Prefix.source decoder rust adversary)
```

This uses the SAME first-record parsed wire, all3 native authenticated maps,
22 indexed payloads (duplicates allowed), both query-loop returns and flushes,
and finish on `materialize out22 flushed22`. There is no source/model verifier
acceptance premise, terminal Checks premise, classifier-no-hit premise,
probability bound, or whole-driver output equality premise. Both annotation
passes and the actual executable extractor proof are connected.

Discharged internally: completeState (from Q1), pairingChecks (source finish
control and local laws), ClosedSum/residualBatch (actual dot and completeState),
opening/claim/polynomial parsers, literal semantic degree guards, transport of
initial fibres/folded siblings, all map identity and two annotation passes,
constructor schedule, and executable extractor fixed-word identity.

Retained unchanged: all Port6AUTH_Query local source/helper premises including
S2CallerFacts, P6Boundary, prepare/geometry/arithmetic/decoder ports, physicality,
sourceCalls1161, actual first-record batch and sampler read containment, reached
parse and literal matching read; named Port4D PairingLaws, all22 match0 frontier,
semantic EquationEndpoint and actual dot interpretation. These local Session A
first-fold/semantic/arithmetic refinements are NOT newly proved here.
Port6CK BodyMatches remains explicit. No retained premise is claimed instantiated
merely because it appears in a record or is a familiar theorem name.

Added input glue identities: stored=first-record.stored; input parsed q tr=some i;
queries tr=some q; source Prepared is S2; actual finish call succeeds on the
SAME final materialized source state. These expose the source producers to be
instantiated; they assert no desired acceptance/model equivalence. All original
adversary/oracle quantifiers remain. This is a sufficient call-level theorem,
not an end-to-end accepted DRIVER theorem or a replacement security headline.

`Port7CLEAN_Extractor.fixed` separately proves executable words=first builder
and extractor rewording fixes the full proof from actual stored parsing and
sampler membership. It needs no acceptance, terminal Checks or no-hit premise.

## Driver progress and blocking dependency

`Port7CLEAN_Driver.first_accepted` derives FIRST physical-entry acceptance from
full source acceptance using the already proved source_enrich law.
`accepted_entry` exposes its exact asSlice public/stored returns and successful
semantic decode. `accepted_stages` exposes the actual TX1 returned checkpoint,
TX2 on that SAME checkpoint and exact TX1++TX2 chronological log.

The next missing instance is not another generic containment law. The driver
accepts `impl : VTop_OracleCode.Implementation`; Port1_Library fixes only library
operations, leaving body7 (prepare), body5 (batches), body18 (resume), etc. free.
The new compiled `Port7CLEAN_TraceObstruction.no_sampler_embedding` proves:
for every source Ops dictionary and H, the valueOnly interpretation returning
exactly `invoke ops call` has an empty driver log and cannot contain even the
sampler's row0 frame. Thus native pure return laws cannot prove the required
embedding. This disproves only the unqualified interface claim, NOT a concrete
pinned effectful frozen driver; no full-source security counterexample is claimed.
The definition inventory has no instantiated VTop body Implementation connecting
those native returns to their effect programs: the actual op7 program is still
a Session A prepare boundary. The op5 P6 sourceBatch is a separate effect program
whose existence/success is proved by Port4B, not its occurrence in impl's log.

Next concrete deliverable: an owned effectful op7 instance with its successful
prepare return and complete ordered sampler trace, and an op5 instance bound to
P6's actual batch program, then prove their occurrence in the accepted TX1/TX2
continuations above. Preserve the actual op18 return/BodyMatches; do not replace
it with the first materialized state without its checkpoint join. Instantiate
S2 reached/input snapshots from that run. This permits first-record batch/sampler
and chronological charged-prefix embeddings and completion/no-hit composition.
It cannot be supplied by assuming an all-driver equality or adding reads to a
new interpretation without proving that interpretation refines frozen source.

No-hit is still OPEN. No replacement premise is adopted. The all-input1161 count,
unchanged runtime StoredCarrierBinding, first-fold/semantic leaves and coherent
release replay are also open. The unchanged additive bound and whole zero-query
contract have neither been weakened nor newly established for deployed code.

## Failed approaches and new evidence

Green final changed targets:001 Terminal,002 Recovered,016 Carrier,020 Extractor,
022 TraceObstruction,023 Accepted,026 Driver. Historical green009/017 are
superseded by later source changes, not counted as final-source validation.
Failed receipts003/005-008/010-015/018-019/021/024-025 are preserved. The memory
failures006/010/011/012/014 came from concrete transcript33 statement conversion;
013 was default-heartbeat elaboration, and other failures are type/namespace/
syntax errors. Replacement: separately proved symbolic transcript_statement,
erased_statement and reached_statement, then checks_to_source. This made016 and
the dependent023 fast. No cap or Lean option was raised, no unchanged resource
failure was retried. No Kani or arithmetic extraction gate was needed.

All results use isolated objects and independently capped 6G/8G/no-swap/64-task
scopes, Lean-j1/-M4400, global serialization and populated reservation admission.
Only final successful matching-source receipts establish claims. Failed axiom
outputs, including sorryAx or unvalidated declaration names, establish nothing.
A single final focused axioms/import audit follows these changed-source passes.
