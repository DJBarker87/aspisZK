# Same-caller View.y1 bytes and all 29 field reads — 2026-10-24

Checked: one accepted complete preparation derives the EXACT `View.y1`
passed to its own Prepared::new, its stored proof range [7031,7495), all 928
expanded bytes, and successful concrete field parses with canonical complete
outputs at every column0..28. The result is exported at the same installed
release op7 Program evaluation and at owned adapter stage1, retaining decoded
public reuse, same preparation/scratch, both physical roots and continuation.

This is ACCEPTED-ONLY source-model evidence. Whole S1/S6, native SDK/runtime/
abort interpretation and the raw <=2^-100 per-attempt security target remain
OPEN. No source adoption or security metric changed.

## Gap closed and before/after statement

The prior `prepare_y1` theorem retained an expansion witness `expanded` and
downstream View arguments `semantic,y1`, but did not state `y1=expanded` or
`view.y1=expanded`. Its byte formula therefore could not be transferred to
the actual claim input merely by quoting that theorem.

The new `AspisS1ValuesOwnedInstallation.prepare_view_y1` starts from the SAME
complete accepted prepare return on its original full carriers and derives:

- actual stored proof range [7031,7495) and stored length464;
- `expandValues stored initial=ok (.Ok (),view.y1)`, initial length928 and
  `view.y1.length=928`;
- for every j<928, the byte in `view.y1` is the actual compact input byte at
  `16*(j/32)+j%32` when j%32<16, and zero otherwise;
- actual source View, semantic child and original new/scratch calls using
  this same View;
- for EVERY source column l<29, a complete eight-word parsed E with
  `ClaimParser.field view.y1 l=ok parsed` and Canonical parsed.

No buffer equality, per-call length law, canonical-input or separately
successful parser/semantic/prepare child is added as a premise. `ops/R/B`
remain explicit source-model installation parameters. The accepted-result
hypothesis remains explicit; this is not unconditional success on every
native input.

## Exact dataflow proof

`S1PrepareBufferY1RecombineV1.y1_recombined` follows the actual
Vec.deref_mut → split_at_mut → both replacements → split back-function →
Vec back-function → RangeFrom reindex path. It proves the back-function's
length guard and the exact concatenated vector bytes, then proves the suffix
returned by RangeFrom equals the second replacement. No setter guard is
silently dropped. This complements the existing semantic prefix theorem.

`S1PrepareBothBuffersV1.prepare_buffers` reuses the complete source control
proof and retains BOTH codec calls, their original inputs/replacements,
`semantic=expandedSemantic`, `y1=expandedY1`, and the same downstream
View/semantic/new calls. Its two generic length hypotheses are discharged by
the native-semantic length theorem and concrete owned-values frame theorem
in `prepare_view_y1`.

`S1WideViewY1V1` proves both nominal View and current carrier View retain the
actual Y1 argument. All original View errors/failure/divergence remain in the
source body. The proof only inverts successful full calls; it does not
replace View with a selected-field token.

## All field reads, without an independent parser premise

`S1ClaimY1ReadsV1.original_payload_y1_fields` consumes the existing checked
OriginalPayloadClaimMeaning and selects point5. Its length29 and exact
source-index ordering prove that every column0..28 actually occurs. Merely
knowing a property of members of an arbitrary short list would not suffice.
The selected-source clause supplies the actual concrete parser call and full
canonical output at that exact column.

The generic helper's Meaning input is NOT assumed by the enclosing caller.
`original_new_y1_fields` derives it with the existing installed preparation
meaning theorem from the SAME source View and original new/scratch calls.
Inactive canonicality is derived from that View's actual parse, not supplied
independently. `prepare_view_y1` then binds those results to the same physical
expansion and `View.y1` bytes above. This reuses parsing/canonicality proofs;
it does not re-prove the parser cone or alter its source.

These are successful reached source-model parses. They do not prove native
field parsing cannot abort on every rejected arbitrary byte string, nor do
they establish native SDK/P6 interpretation by themselves. The mathematical
range facts and canonical outputs must retain that accepted-only scope.

## Enclosing consumers

`S1TopPrepareY1ProvenanceV1.source_y1_provenance` identifies the full current
Prepared and gamma scratch returned at the physical op7 ABI, with the exact
actual View/semantic/new calls and all Y1 clauses. Its Y1Provenance definition
is an explicit existential CONCLUSION, not an assumed source contract.
`installed_y1_provenance` starts from the same accepted installed Program
evaluation, with the per-H P3 interpretation, and derives both <=115 reads
and this provenance. The earlier ordered source effects/value theorem is
used to obtain the source call; no new all-H/native-dictionary assumption is
invented.

`S1ValuesOwnedStage1ViewY1V1.owned_stage1_view_y1` exports the same strengthening
from the owned adapter's single accepted stage1. It retains the actual decoded
public statement and split, release None, same Prepared/scratch, both physical
roots, checkpoint continuation, and full actual View/semantic/new witnesses.
It supplies all29 field parses on that View.y1. No independently successful
child execution is added.

## Exact remaining obligations and source decisions

This closes the missing codec-buffer→actual View→claim-field dataflow at the
installed/owned source-model boundary. It is not an actual SDK/account
execution theorem. S2 remains transferred; native SDK/input-retention and
cross-transaction reconstruction bindings retain their existing owners.
Concrete semantic R/B source-child instances, native numeric/Std/runtime/
abort/effect lowering, canonical frozen parser/query/root association, final
StoredCarrierBinding/release identities and the whole security experiment
remain open. The lead's release-call-site/count integration is separate and
not duplicated here.

The adopted29cb/25866 authority and current artifact authority remain as
corrected in S1-POWERS-CALLBACK-SCRATCH-20261024.md. Source/model control and
native positive codec evidence are reused under their exact pins; no new
source freeze is selected and no ELF or runtime measurement is claimed.
No additional source decision is required by this additive proof packet.
Future source/backend changes still require equivalence/integration/re-pin.

## Validation

Source-only focused-extractor-proof-packet-v1 metadata:
`s1-y1-caller-{targets,import-pins,source-pins,tool-pins,failures}.json` under
`evidence/s126-current-caller-20261021`. Seven accepted targets:
185.0945392921567s selected wall time,peak3801939968 bytes,zero swap;
all #print axioms reports are standard-only. Exact source/tool/direct and
transitive import hashes, targets and statuses are retained. Compiled objects,
executables and LLBC are not distributed.

Every local Lean job used the atomic known-owned lock,-j1,-M4400 and warm
objects, one job at a time. Smallest changed target first, then changed
consumers; final parent strengthening justified its focused recompilation.
No unchanged package/manifest replay or heavy NUC job ran. The one failed API
probe is retained as failed, excluded from proof evidence. Resource options
were not raised. This is focused cached validation, not a coherent release
replay or native machine-semantics certificate.

```
python3 tools/s1-y1-caller-20261024/check.py
```
