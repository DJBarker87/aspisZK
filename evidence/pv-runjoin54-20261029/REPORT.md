# Runjoin54 — top-down publication composition

Entry: 1adf3ca50f50b8983de4eeb9609731a1301ca463, branch codex/pv-runjoin-20261026.
Budget: 100 Lean attempts, IDs 66900–66999; 66997–66999 audit-only; zero Kani.
Step (4) has not started. Protected prefixes remain read-only.

The target is the exact `PV_RJ4IDB.OpenInputs.RUNJOIN_PUBLISH_COMPACT` read
with git show from candidate revision 2a484b7a681b16f1904cd781a7ac38d4ecef3219.
Its eleven-module interface closure is reused read-only with source/object
hashes and every imported object fingerprint checked before use.

## Composition design

The first local theorem extracts the actual prepare, salt, finish and publish
successes from `prover.prove_from_semantics`, without replacing any source
call. The conditional typed skeleton will expose seven named links, retaining
r24/sampler, common sample, backend producer, FinishContext, query append,
node append/indices, and publication ordering separately.

Whole ledger rows removed: none. Endpoint and TrustItems unchanged.

## Recorded workflow error

66939 accidentally resubmitted the unchanged failed source from 66938: an
exact-text replacement missed its indentation. Both failed, neither earns
credit. The subsequent source is changed, and the own-input pre-submission
wrapper now rejects any source hash previously rejected for that module.

## Checked top-down skeleton

`R1Z.PV_RunJoin_PublishSkeleton54.complete` passed at **66904**, the fifth
attempt (source 003aaceec2, scope 2.04 s, peak RSS 4,514,455,552 bytes,
zero swap). Its conclusion uses the original, unchanged candidate constant:

```lean
PV_RJ4IDB.OpenInputs.RUNJOIN_PUBLISH_COMPACT
  (@actual (types base) (selected base heap box ops) I runs)
  (@published (types base) (selected base heap box ops) I runs)
```

The binders are `base`, `heap`, `box`, `ops`, the indexed family `runs`, and
seven standalone `PV_RunJoin_Link_*` Props: R24Sampler, CommonSample,
BackendInput, FinishContext, QueryAppend, NodeAppend and PublishOrder.
`OpeningImages54.complete` consumes `ProverCommitOpeningModel53.exact_images`;
coefficient caller provenance uses `CoefficientsActual50.complete`.
`PublishReach54.complete` extracts the actual prepare, salt, finish and
publish calls from successful `prover.prove_from_semantics` runs.
`ProverCommitPublish43.assemble_loop` closes the ordered assembly step.
The link definitions are unchanged since their accepted skeleton revision.
No link is an axiom or an instance, and none restates this complete-run
conclusion. The actual definitions and exact link statements are in
`PV_RunJoin_PublishSkeleton54.lean`.

**Scope of the indexed families:** `actual` projects the complete Result of
`prover.prove_from_semantics` to optional bytes; `published` tests that same
source outcome and, on success, uses the independent ordered model assembly.
It never reads the actual proof bytes when constructing the model bytes.
Failure, divergence and inner verifier errors produce `None`. The family
starts with the source semantic/backend inputs. It has not been instantiated
as the native caller's entire admitted-prefix family. This conditional
composition is not a proof that a native publication producer has been
installed.

## Link status

| Fixed link | Status |
| --- | --- |
| R24Sampler | **Discharged**, `LinkR24Discharged54.complete`, 66968. Four exact accumulator residues, canonical output and actual byte-sampler canonicality. |
| CommonSample | Open. Canonical neutral map equality, both errors and both fallback rows are proved; original `toRP`, frames, stored fields, coefficient trace, map_err and complete returned-record composition remain. |
| BackendInput | Open. Actual caller initialization/build/commitment producer, message association, length 29 and canonical coefficient derivation remain. |
| FinishContext | Open. Actual folded leaves/tree/root, tag 30, final fold, tag 31/32, public checks and front-field association remain. |
| QueryAppend | Open. Actual 22 source query appends must produce the ordered six parts per query. |
| NodeAppend | Open. Six multiproofs, sorted/deduplicated publication indices, padding and byte/error association remain. |
| PublishOrder | Open. Actual local serializer, constants/guards, compact semantic and claim fields, opening images, query and node appends must produce the model assembly. |

`LinkR24Discharged54.publication` is the exact typed conclusion with the first
link removed and the other six retained, accepted at 66968. No link is
weakened. No new whole ledger row is removed. V038, V045, V163, V165, V167,
V244, V258–V260 and V262 receive no whole-row credit.

## Additional established scope

The four r24 cells are independently compiled and recomposed through a named
source equation. Scalar residue laws and canonical injectivity identify the
four outputs with the owned complex/quartic formula. No arithmetic chain or
large recurrence is normalized as a monolithic source proof. The neutral
circle comparison preserves full Results through inverse failure/divergence,
singular/subfield errors and both fallback rows. The authoritative R72 map
adapter is checked separately from the owned Types authority.

The retained public-preparation sampler's checked predecessor, shift, byte
indices, multiplication, addition and stores are associated with the neutral
wrapping sampler through named equations. Loop identities use their step
functions, not finite unrolling. This connects canonicality to actual source
computations; it does not assume sampler success or canonical producer input.

No package-wide or frozen release manifest replay, native differential,
Kani, Rust build, extraction, ELF operation or step (4) is claimed. V370 and
the D381/D386 compiler boundary, deployed op79/op254, disclosed and
observerOracle installations remain explicit. The same eight endpoint
fields and three TrustItems, guards, collision/public-address conditions,
observer/simulator/coupling/events, failure independence and side-channel
scope are retained. Frozen Rust/client source equals 82566acdfb. No key was
accessed, destroyed or cleaned up; no shared sources/caches were overwritten.
