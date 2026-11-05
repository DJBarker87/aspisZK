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
