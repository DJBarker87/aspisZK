# NGX retained failures

K001/K002: own frozen archives omitted unchanged workspace path dependencies.
K003/K004: own frozen include sources omitted. No verifier launched; inputs
were added unchanged, not validation weakened. K007: own local oracle hash
omitted Copy required by Digest32; fixed with reference-wrapper Copy/Clone.

L003: requested absent next_row helper during a diagnostic; no proof credit.
L013: requested Prefix.payload in the wrong namespace; available definitions
were printed, no credit. L014: conditional rewrite and row substitution errors;
L015 corrects the proof and compiles with standard axioms. Failed draft prints
containing sorryAx are excluded; no failed object is imported as credit.

K010, constructor: native assertion comparing the entire38-byte constant domain
with memcmp exceeded the35-iteration harness bound (unwinding failure, not a
timeout or implementation mismatch). Replace ONLY that comparison by exact
static-slice pointer AND length identity, which proves the same borrowed-domain
bytes without an unrelated comparison loop. No cap, timeout, unwind bound or
caller domain is raised. The original verdict is retained and never credited.

L030: domain constant is irreducible, and own binder name `public` was reserved.
L031 inspected the canonical loaded definition: every one of the38 bytes is
correct; this was NOT a source/model mismatch. L032 explicitly unfolds that
small constant and proves exact bytes/length with standard axioms.
L033: an unnecessary explicit legacy S1 module import collided with the
canonical Phase owner. L034 confirmed Code/run/sampleBlock/newTranscript are
ALREADY present in NGK's coherent environment. Remove that legacy import and
reuse those existing owners; do not duplicate or redefine them.

K024: own input error: passed short harness name despite --exact. Kani rejected selection before CBMC. No verdict or credit; K025 uses the original fully qualified prefix_value name unchanged.

K026: strict source preflight rejected the newly extended own harness because NGX_SOURCE_PINS still pinned the previous stage. No Kani process started. Pins regenerated from committed overlay inputs for K027; gate unchanged.

L049/L052 diagnostic unknown names are excluded. L050 sampler draft accidentally resolved a different sampler namespace after the imported wrappers; L051 explicitly selects the adopted PublicPreparation owner and passes. L053 used unsupported namespace alias syntax; L054 spells both owners completely and passes. L055/L056 generic Code.bind proof required its fully qualified definition and explicit induction rewrite; L057 passes. Failed draft axioms (including sorryAx) are never imported.

E001 extraction: Charon succeeded but left public_bytes as an external declaration. This is an incomplete body selection, not a proof of the producer. Excluded from credit. E002 adds explicit source includes to traverse the actual serializer and semantic public constructors, with unchanged frozen source and tools.

E002 actual serializer extraction: Charon exit0; Aeneas exit2 at SemanticPublic (non-ADT/opaque type cannot be expanded). This is an incomplete own include selection, not evidence of a source/model mismatch or a host launcher fault. A future extraction must include SemanticPublic and the reached transition carriers explicitly. Both allocated extraction runs are consumed; neither E001 external axiom template nor E002 incomplete body is imported or credited. Frozen lock unchanged.

L058: the error-continuation draft needed an explicit core.result.Result.Ok constructor type; L059 passes with standard axioms. L067/L068 inventory diagnostics used a tuple pattern that the loaded syntax rejected; L069 uses explicit entry projections and prints the actual canonical owners. Neither diagnostic is proof credit. Stage3 validator initially parsed NGT's pretty JSON as a single last line; own parser corrected to parse the entire JSON output, retaining all checks.

Own cleanup script initially looked for client-created binary pins on the host. It stopped before deleting any scratch; the pins are now supplied from the local L065 receipt and checked against the retained binaries. No launcher/shared infrastructure was modified.
