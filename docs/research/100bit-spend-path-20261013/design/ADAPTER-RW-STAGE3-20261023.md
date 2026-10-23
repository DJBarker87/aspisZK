# Owned adapter Stage 3

Branch `codex/cx-adapter-rw-20261023`; resumed from `b94f86c9ca`.
Candidate source is Stage 2's shipped owned implementation at `572236f37d`.
Stage 3 is PARTIAL. Complete native Required14 and the release target remain
open. No adoption or push.

## Extraction and trust boundary

Charon004 and Aeneas003 extract both complete owned callers from the actual
candidate source, including owned ASQ8 authentication, registry admission and
reconstruction control. They do not extract a handwritten caller copy.
`generated-v3` retains the successful emission. Its old TypesExternal template
is a stale file from an earlier attempt: Types imports no external types, and
contains both enum layouts. It is not an input to the adapted model.

The initial `AdapterRwTypes` / `AdapterRwModel` used the existing named-discriminant adapter,
remove generated resource settings, and replaced 59 external operations with an
explicit `Ops` parameter. No operation is installed merely by parameterization.
Aeneas clipped one deeply nested registry tail's indentation at column68;
`repair_layout.py` repairs whitespace with checked non-whitespace token equality.
`adapt_extract.py` preserves the emitted branches, calls, argument order and
error mapping, and records raw/adapted hashes and all operation names.

Lean002 (types) and005 (whole model) pass on the capped host. Attempts003/004
are retained formatting failures, with recovery `sorryAx` excluded from evidence.
All successful model audits contain only standard Lean axioms. SDK snapshot and
write wrappers are outside this extraction, as designed. Runtime admission,
allocator behavior, child effects and source-to-SBF interpretation remain explicit.

## Final extraction and actual accepted-call results

Final inputs are Charon008 / Aeneas007 / `generated-final`. The underlying
three production Rust files are byte-identical to this worktree, with their
hashes in `source-refinement.json`. The source revision is `572236f37d`;
subsequent proof/tool commits do not change Rust. This is the implemented
Stage-2 adoption candidate, not a claim that the frozen release was replaced.

The final model has **54 explicit operations**, including complete carriers
for opaque verifier/decoder/encoder/PDA/digest/error/emit operations. The reached
`Option::ok_or` and `Result::clone` bodies are extracted, rather than assigned
arbitrary successful results. Constants have their transitive initializers.
`AdapterRwConstants` proves the small constant DAG through generic checked-scalar
lemmas, emitted by `gen_constants.py --check`; proof57607 and prefix688 do not
remain arbitrary constant callbacks. No huge numeral/recurrence evaluation.

`AdapterRwCuts.stage1_call` derives the actual proof/public account reads, SAME
decoded and validated statement, semantic public projection, exact selected
range, same `first_decoded` invocation and same returned checkpoint. Its separate
`stage1_checkpoint_length` derives the returned-vector/observed-checkpoint-data
length equality; it does NOT replace either length by1768 without a snapshot
representation theorem.

`AdapterRwCuts.stage2_call` derives the actual extracted `validate_asq8` success,
proof/checkpoint reads, SAME statement's full1880 encoder result, exact tx2
arguments with observer None, successful tx2 and SAME statement's emitter call.
The whole `validate_asq8` body and both authentication bodies are in the model;
none is replaced by an opaque authenticated-caller hypothesis. Individual value
children remain opaque, with their full error and return carriers.

`AdapterRwAccepted.first_call` specializes the actual TX1 range to688..58295
and derives raw proof-account length58295 from its guard. `first_proof_shapes`
then proves selected length57607 and full prefix/suffix decomposition using
the checked range operation's standard-library specification.
`AdapterRwLeadInputs.first_byte_fields` exports those SAME invoked bytes to
`MultiproofConeCanonical.bytesOf`, the actual lead Byte carrier.
These accepted-run implications never assert a child succeeds in advance;
outer fail/div and inner Err branches cannot become an invented Ok.

## Per-function source/extraction relation

The source-to-model relation here is extraction of the actual functions, under
the existing Charon/Aeneas translation boundary, plus the explicitly listed
emission adapter. It is not differential equivalence to a handwritten reference.
No Rust function body, child call, query prefix or error branch was rewritten.
The raw/adapted hashes and complete external-operation map are retained. Source
to SBF compiler/ABI/runtime interpretation remains separate from extraction.

| Native function(s) | Extracted definitions in `AdapterRwModel` |
| --- | --- |
| `OwnedAccount::key`, `owner` | `r1_pool_adapter.owned.OwnedAccount.impl.key`, `.impl.owner` |
| `OwnedAccount::data`, `data_len` | `r1_pool_adapter.owned.OwnedAccount.data`, `.data_len` |
| `require_readonly_buffer`, `require_readonly_account`, `require_verifier_checkpoint` | Same names under `r1_pool_adapter.owned` |
| `require_distinct_accounts` | Same name and both emitted loop bodies |
| `require_zero` | Same name and emitted loop body |
| `authenticate_invariant_release_registry` | Same name, including both registry versions and all PDA/metadata branches |
| `authenticate_asq8_accounts` | Same name, with full reconstructed account/value carriers |
| `validate_asq8` | Same name, including request bindings, clock Result, account authentication, scanner and reconstruction call order |
| `stage1_owned`, `stage2_owned` | Both complete same-name callers |
| `observer`, `first_decoded` | Actual native wrappers; `Cuts.observer_none` / `first_decoded_call` |

SDK `snapshot` and the SDK `stage1`/`stage2` boundary wrappers are outside the
owned continuation extraction. The existing SDK trust licenses their primitive
acquire/dereference/drop/write steps; it does not by itself prove native Vec
allocation/copy, wrapper cut placement, metadata interpretation or persistence.
Those source/glue obligations remain open. No Kani fallback was needed for the
listed owned continuation functions: all extracted. No Kani result is claimed
for the SDK wrappers or the excluded optional helper below.

Optional Charon006/007/Aeneas005/006 exposed `checkpoint_size`/`final_len` too.
Lean039 found the pinned emitter/library mismatch: `Usize.wrapping_shr` was
applied to a Usize shift count, but this library expects U32. That item was
stopped; no cast or arithmetic replacement was inserted. Final008/007 retains
checkpoint sizing as the same explicit operation boundary used before this
optional extraction. Enum-fold/shift refinement and a concrete sizing instance
remain open. `generated-v5`, Lean039 and all receipts retain the obstruction;
Aeneas006 was not pointlessly compiled against the identical shift obstruction.

## SDK entry bracket

`AdapterRwSdkSnapshots.shared_bracket_restores` / `entry_bracket_restores`
prove exact acquire/drop bookkeeping restoration under RuntimeEntrypointAdmission,
including duplicate-key/shared-cell entries. `acquired_valid` discharges validity
of the temporary shared guard. `native_entry_shared`, `native_entry_read` and
`native_entry_drop` instantiate ONLY the corresponding existing trust fields;
the read observes precisely the entry account payload. Native relatedness at
the copy/drop cut is still explicit. In particular these theorems do NOT treat
`to_vec` allocation as an inert ambient-state step. S2TrustedSdkBorrow's fifteen
fields and RuntimeEntrypointAdmission are unchanged.

## Required14: field-by-field disposition

“Discharged at TX1 cut” below refers to the actual selected argument, not an
arbitrary externally chosen `stored`. A complete native `Inputs` observation and
`S2CallerFacts` inhabitant have NOT been constructed. There is one proved local
field value, three conditional field implications, and ten open global fields.
This is not a claim of1/14 complete native refinement.

`ChildInputRetention` is an explicit, OPEN Prop hypothesis about reached sites
inside each successful first/second child, on the same actual arguments and
returned value. It is NOT instantiated by S2G's pure value instance. Its fields
are shown verbatim in `AdapterRwLeadInputs`; no new trust item or axiom is added.
`input_fields` requires matching proof/public arguments for both actual child
calls. Source-level equality of those arguments across transactions is still an
independent obligation. `observer_field` does not require that equality.

| S2CallerFacts field | Status | Exact evidence / remaining obligation |
| --- | --- | --- |
| `proofBytes` | Conditional on named child hypothesis | `LeadInputs.input_fields`, under `ChildInputRetention.first/second` and SAME proof argument at both actual calls. Native snapshot identity across transactions and observation reification remain open. |
| `publicBytes` | Conditional on named child hypothesis | Same theorem/retention hypotheses; SAME public argument additionally needs the full forest reconstruction/1880-byte encoding roundtrip. S2K's payment216 encoder theorem does not provide that roundtrip. |
| `proofSuffix` | Open globally | `Accepted.first_proof_shapes` / `LeadInputs.first_byte_fields` discharge the actual TX1 prefix/suffix equation. Need TX2 same-buffer binding and the actual `c.proofAccount` observation, not merely a length or address. |
| `proofLength` | Discharged at actual TX1 argument | `LeadInputs.first_byte_fields`: `(bytesOf selected.val).length = 57607`, with `selected` the SAME successful native-owned first-call argument. Global `stored` must be this argument; shared-site identity is not inferred. |
| `checkpointBytes` | Open | SDK write/copy cut binding, inter-transaction retention and actual save/tx2/resume child-input provenance. No persistence is inferred from readonly flags. |
| `checkpointLength` | Open | `Cuts.stage1_checkpoint_length` proves equal observed lengths only. Need the entry snapshot's actual1768-byte copy/representation invariant and concrete sizing/retained checkpoint port. |
| `nodeViews` | Open | Install the actual parser/physical-slot child-input provenance for SAME stored bytes/parsed wire. Existing P6 slot model theorem alone is insufficient. |
| `y1Input` | Open | Tie the actual child scan argument to selected7031/464; S8's parsed scan theorem does not establish this native site input. |
| `observerNone` | Conditional on named child hypothesis | `Cuts.observer_none`, `first_decoded_call`, `stage2_call` prove actual None dispatch. `LeadInputs.observer_field` supplies the full field only under `ChildInputRetention`. |
| `reachedPrefix` | Open | Concrete child internal reachability/schedule and native two-transaction observation join. |
| `callOrder` | Open | Same-run ordered site/clock interpretation, including child internals and the transaction boundary. No invented ranks are substituted for source clocks. |
| `accountFrame` | Open | Complete native child effect frames, owned allocation/copy interpretation, SDK write cut and full account-record observations. Local primitive frames are not a whole-caller frame. |
| `writtenMetadata` | Open | Native full metadata interpretation and account2 copy/child-effect composition; the trust record does not observe all ambient metadata. |
| `oracle` | Open | Native SolanaDigest/hashv reification and the total raw-oracle interpretation law. Existing reified ordered-event theorems are not a native ROM implementation theorem. |

Existing child contracts remain scoped as in S2G/S2I/S2K. No native whole-child
contract was strengthened or marked installed. The new conditional input port is
an explicitly added implication premise, not an assumed discharge. Existing
unresolved native decoder/encoder, verifier effects, allocator, emit/clear syscall,
PDA, cross-transaction, backend/oracle and source-to-ELF obligations are retained.

## Verification and next deliverable

Focused build packet and per-attempt metrics: `stage3-manifest.json`; raw exact
commands, base source revisions, source SHA256s, selected dependency hashes,
exit/wall/RSS/swap and complete printed axiom lines remain beside each attempt.
Private host objects only: no shared `.olean` or another worktree was rewritten.
No binary, LLBC, `.olean`, ELF or key enters the commit; artifact pins retain
SHA256 plus size. All host scopes use6G high/8G max/Swap0/Tasks64 and reservation
checks. Rust extraction compilation is optimized release; measured time is in
compilation/translation, not arithmetic elimination. No memory kill, increased
cap or unchanged failed rerun occurred. Failed default-heartbeat inversions were
replaced by head-only inversion, early Result elimination and generic scalar
lemmas. Failed elaboration recovery `sorryAx` lines are retained but excluded
from successful evidence.

The final focused union audits every added theorem against the selected cache
objects. It is not a coherent frozen release-manifest rebuild. The full manifest
was not started because the native child/source/observation predecessors are not
closed. Stage2 runtime/SBF/reproducible gates are reused, not rerun: this stage
changes no production Rust or frozen binary. Budget usage is reported by the
machine-readable audit; Kani0/60.

The next concrete deliverable is the native entry-snapshot Vec/copy and metadata
interpretation at the actual SDK cuts, plus a source-indexed first/second child
input/effect port on these exact extracted carriers. Then establish same proof,
public reconstruction and checkpoint retention across the two actual calls,
and install the remaining parser/S7/S8/P6/SDK write/backend joins. The full native
Required14/release target is **not yet established**.

Final audit: `python3 tools/adapter-rw-20261023/audit_stage3.py` passes.
Stage3 Lean attempts002–048: **47/100** (18 successful focused builds,29 retained
failed attempts); **Kani0/60**. Final current-source predecessors are types002,
model040, scalar041, cuts042, constants043, ranges044, accepted045, SDK025 and
lead-inputs047. The changed model dependency is why scalar/cut/constant leaves
were rebuilt; unchanged types and SDK leaves were reused. Runtime001 is reused
Stage2 evidence and is not charged to Stage3.

Final `AdapterRwStage3Audit` at048: exit0,2.047613526s,4358040KiB peak RSS,
swap0; **52 complete standard-only axiom reports**, including the three reused
runtime-entry theorems. Maximum Stage3 Lean RSS was4389132KiB (lead-inputs047),
with no swap. `stage3-manifest.json` retains all attempts, complete multiline
axiom reports, exact limits and current-object pins; source matches are checked
for all11 final modules. Native source capture equality and mechanical adaptation
reproduction also pass. Failed attempts remain excluded from theorem evidence.
