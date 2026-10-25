# Stage 4: checkpoint provenance without authentication circularity

SdkD_WriterSource.returned derives literal digest replies and source-selected
bytes from an actual writer success, with no canonical-state equation.
SdkD_WriterCells/WriterRoot1 prove the sparse root slots symbolically.
SdkD_WriterRoots.returned derives the saved checkpoint's two raw root slices.
SdkD_WriterQueryCells/WriterQueries derive all22 raw four-byte query cells,
and the1768-byte writer width, without canonical arithmetic or authenticated
openings. SdkD_ReaderRoots/ReaderQueries derive the returned roots/query words
from the actual successful source reader's physical fields and cursor.
Their writer_reader theorems prove exact root and whole22-word query-array
identity across the SAME saved checkpoint byte equality. No ten-step model
state, packed recovery, hash injectivity or replacement reader is assumed.

SdkD_Tx1Suffix/Tx1Run additionally retain physical folded-root reads together
with the complete old Tx1Q Run witness, so its preparation, query, flush and
writer all use that SAME p/root. The extra zero-call law is an output.
SdkD_Install fixes source TX2 folded offsets/unwrap, with full dictionary
commutation proofs; these previously arbitrary slots are specialized, not
claimed equal to every possible old dictionary.

SdkD_Nonvacuity.instance_exists constructs the source-site child and both
accepted-only marks for EVERY installed dictionary, without requiring an
accepted call. The removed child/mark arguments therefore impose no new
restriction on the previous acceptance class. This is not a new joint
inhabitation proof for ALL remaining runtime/crypto/extraction premises.

64 Lean attempts used;0 Kani. All new successful top theorems print only
standard axioms. Full per-attempt metrics/source/deps/commands are retained;
no capped job failed from timeout/memory and no limits were raised. The only
review stop is038 as documented.061 queries roundtrip:exit0,2.040006858s,
5210860KiB RSS,swap0;059 roots roundtrip:exit0,1.921260526s,5197576KiB,swap0.
No shipped/cfg(kani) change, ELF rebuild trigger, package replay or key activity.

Top authenticated_S1 and global source-experiment/frame/budget instantiation
remain OPEN. These checked raw roundtrips remove the circular need to use
state arithmetic to identify the two batch inputs; they are not themselves
full premise removal. Replay security term remains6*(Q+1040)^2/256^32.
