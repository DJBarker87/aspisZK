# Checked SDK public-byte binding and S1 caller consumer

This supersedes the unchecked-SDK-bridge status in
S1-S6-ACCOUNT-WITNESSES-20261024.md. The missing public-buffer association is
now a checked result at the existing approved D188/D189 interpretation boundary.
S1 and the complete deployed S6/release result remain open; no 100-bit claim.

## Enclosing obligations actually established

`AspisS6SdkStage1ReuseFactored.accepted_sdk_stage1` in
`S6SdkStage1ReuseFactoredV1.lean` starts with ONE accepted composed native first
wrapper. From it, the theorem derives:

- the actual returned heap is the computed checkpoint write of the returned Vec;
- the public bytes are the original Entry buffer behind actual SDK data cell1,
  with length1880 derived from the successful source read/deferred-error branch;
- the concrete decoder and original nominal decoder accept those same bytes;
- the concrete encoder reconstructs all those same bytes from that statement;
- the actual concrete firstCurrent call on the same public/proof/split returns
  the same checkpoint (its fixed first/first_decoded installation selects None);
- the complete public-account observation after the write equals its initial
  native SDK observation, including metadata fields absent from OwnedAccount.

The original byte/account identity, owned acceptance, successful child calls,
post-write heap and public-account frame are conclusions. None is an extra
premise. Original first_decoded full-Result equality and observer None proofs
are reused; this theorem is ACCEPTED-ONLY on whole wrapper acceptance. Allocation,
copy and cleanup errors/abort behaviour remain in the unchanged wrapper; no
whole-native TOTAL statement is made.

`AspisS1ValuesOwnedInstallation.sdk_stage1_account_numeric` in
`S1SdkStage1AccountNumericV1.lean` consumes the SAME SDK wrapper acceptance and
specializes its extraction to the concrete existing expansion/preparation/
round-child installation. It retains the full earlier S1 conclusion on the
SAME public/proof/account witnesses, and adds native public-buffer/data-cell
identity plus computed checkpoint write/full public observation frame.
The conclusions include actual indices/reads/proof suffix, decoded full
statement, exact compact split, preparation/roots/scratch/continuation, actual
View/Y1 bytes, semantic/Prepared::new calls, all29 canonical Y1 fields, and
canonical alpha/extra/before_z1 of the same returned semantic object.
It invokes the checked account-witness theorem; no reconstructed-statement
identity or separately successful preparation/semantic child is introduced.

## Exact retained premises and quantified implementations

Both theorems retain the project's existing approved boundaries:

- full `Library W (Nat → Record)` and `S2TrustedSdkBorrow L`;
- the actual copy operation with `TrustedStd copy`, private `Allocator A`;
- full Entry/world plus `RuntimeEntrypointAdmission L e world 3`, whose fields
  are initial runtime eligibility and `L.related world e.heap`;
- full `AeneasExtraction (install adapterOps vops) native1 native2 hashv`:
  stage1/stage2 source interpretation and the exact digest wrapper association;
- the ONE accepted complete first-wrapper execution with actual private final
  state, checkpoint Vec and returned heap.

There is no new SDK internals certificate. These are the approved standing
interpretations, not freshly proved Rust/SBF identities. The S6 theorem is
universal in retained adapterOps/vops. S1 fixes vops to the existing concrete
expansion/preparation/round installation, retaining base Ops and FinishModel B.
Claims/Terminal and remaining native primitive/domain/effect obligations are
not silently instantiated. Full extraction dictionaries contain no caller
output/frame conclusion. Their concrete same-installation association in the
enclosing ALL14/child/event/mark/release environment still needs consumption.

## Dependency factor preserves complete source declarations

The full original SDK import closure could not load below -M4400. The import-only
probe established that obstruction before new theorem evaluation. Investigation
found that even importing MultiproofConeCanonical solely for bytesOf loaded
12,430 modules. The replacement is a proof-source dependency factor, not a new
SDK model or a narrowed account carrier.

`S6SdkDependencyFactorV1.lean` copies exact declaration spans from immutable
research97caa13d92, retaining IDENTICAL original namespaces. It preserves the
complete Account/Record/Entry/Heap/Library/runtime/allocator/extraction carriers,
all fields, both first and second wrapper bodies, and their selected proofs.
Only import selection and surrounding namespace/open boilerplate are factored.
The complete operations/types/selected proof texts in each span are unchanged.
bytesOf is copied exactly; its actual SqueezeOracleBridge.decodeByte dependency
is imported normally. Existing SDK/std/trace/privilege proofs are imported.
No opaque replacement, simplified byte carrier or custom axiom is introduced.

`factor.py --check` reconstructs all14 selections from immutable git source,
checking complete source hashes, exact selected body bytes and complete output.
Both original and new failed attempts are retained. The first factor still
imported the whole multiproof module and failed at the same memory cap; after
replacing that import with its exact bytesOf declaration it passed. No cap rise,
new host build, backend modification or resource-option override occurred.
The accepted SDK bridge differs from the earlier complete candidate only in its
import and consumer namespace, checked byte for byte by check-factor.py.

This is a CANDIDATE proof-dependency factor, not a coherent rebuild of every
original textual module. It declares the same names, so it must NOT be imported
alongside unchanged original modules that redeclare those names. Consumption
requires an explicit proof-source factor/re-export adoption and import re-pin,
or the lead's checked logical-declaration reconstruction using the original
matching declarations. That coherence/re-pin obligation is real and remains;
source text equality alone is not called a full mixed-cache release proof.
No production source, protocol, features, ELF pin or another owner's worktree
changed. No production adoption decision is requested. S2 ownership stays with
its successor; this work consumes/copies published definitions for S6 only.

## Validation and remaining work

Smallest factor first, then SDK bridge, then S1 consumer, each one local job
under the atomic lock at -j1/-M4400. All three passed: combined42.70288966642693s,
maxRSS3,888,300,032B,swap0,15 standard-only axiom reports. Individual receipts
record exact commands, revisions, dirty source hashes, tools/imports and output
hashes. Source-only import manifest records the selected cached closure; no
compiled objects are distributed and no unchanged full replay ran.

Source-only focused-extractor-proof-packet-v1 evidence is under
`s126-current-caller-20261021/s6-sdk-first-factor-20261024`, individual target
receipts and `s6-sdk-first-factor-import-pins.json`. Validate:

```
python3 tools/s6-sdk-first-20261024/check-factor.py
```

S6 remaining: coherent source-factor/ALL14/child/event/mark same-installation
consumption and release re-pin/actual artifact association. The former missing
SDK public-byte/frame association is now an output at the named approved
interpretation boundary, not an additional caller premise.

S1 remaining: native Claims allocation/initializedness/cleanup/full-loop binding;
concrete Terminal; remaining mask/eta/terminal domains; native/Std/abort/effect
and final caller/release joins. Kani's uninit-checks ICE remains unresolved.
Shared probability/oracle-law/artifact/coherent final replay gates remain open.
No security target or prior failed validation has been redefined as complete.

## Later enclosing-cut and compiled-equivalence addendum

See S1-S6-ENCLOSING-CUTS-20261024.md. The accepted SDK parent now yields reuse
and S1 preparation/numeric on EVERY matching published enclosing SourceCuts.
A read-only compiled declaration comparison exposed a generated first matcher
difference; a checked all-outcome equality to the pinned original body resolves
it, and two enclosing consumers use that equality. Source/coherent-module/event/
release re-pins remain explicit; no original failed target was relabelled passed.
