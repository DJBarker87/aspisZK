# P6 source-step equivalence certificate

This is the established P6 route's external source-equivalence evidence, not a
Lean axiom asserting the law. The installed Lean reference is separately extracted
and checked. Kani uses the actual field decoder implementations and exact copied
shipped bodies, pinned by source-pins.json. No verifier/model/shipped byte changes.

The comparison domain is every 57,607-byte input, with no canonicality premise.
All source ranges are in bounds on that domain. On a malformed shorter slice the
reference may return Err instead of the source's bounds failure; no equivalence
outside the deployed length is claimed or required by the accepted theorem.

## Covered steps and composition

- Kani002 checks the entire opening loop body on every arbitrary 832-byte opening:
  four slots, all 26 M31 lanes per slot, the K lane, both C2 K lanes per slot, and
  the final four wide values. The exact Result is compared, not just success.
  It establishes equivalence to opening_scan, including rejection. Source interleaves
  the C1/C2 checks; reference groups their regions. Both have empty effects, and
  every rejection is Parse, so the observed Result is equal despite that ordering.
- Kani003 checks all 29 compact y1 chunks against check_values for arbitrary464
  bytes. It compares is_ok; both carriers are Unit on success and have the single
  reachable error (NonCanonical, mapped by the exact From body to Parse).
- Kani004 checks the exact echeck loop on one arbitrary32-byte chunk with k=false,
  comparing full Result against canonical_words. This is the generic wide-step
  law; it is not restricted to honest or canonical fields.
- Kani008 checks chunks_exact32 indexing, remainder0, next-loop length and
  slice pointer/length identity at an arbitrary ordinal of EACH of the three
  actual source ranges: [7495,7527), [7527,7751), [7783,10055). It includes the
  final ordinal and every malformed byte input. Pointer+length identity of shared
  immutable slices gives identity of their bytes, without a huge byte-index mux.
- Kani007 checks actual opening(proof,i) pointer/length against the owned opening
  offset for arbitrary deployed bytes and arbitrary i<22. Thus Kani002 applies
  to every iteration of the actual22-step outer loop, on its original stored
  bytes, not an independently chosen opening.

Composition is the ordinary effect-free loop induction under existing P6 Rust
execution semantics: an empty chunk/opening suffix returns Ok; a next failing
step returns Parse and evaluates no later child; a succeeding step continues on
exactly the next checked slice. The wide regions have1,7,71 chunks. Their word
checks concatenate into canonical_words on256 and2272 bytes; no remainder is
ignored because each source length is divisible by32. The first two regions
combine [7495,7527) and [7527,7751). The outer loop has exactly22 openings, with
last end28359≤57607. y1 is checked first and has29 complete16-byte chunks.
This gives the same Ok/Parse result as reference.scan for all deployed inputs.

There are no mutable parameters, global writes, digest/oracle/observer calls,
allocation or IO in either scan. The compared effect trace is empty on success
and rejection, including every rejected prefix. No adaptive query reordering or
oracle-erasure claim is made. Bounds/overflow checks are covered by Kani and the
fixed ranges. Nominal Result/Error transport is explicit in Op4P_Install.

## Attempts and trust

Eight Kani invocations (including the rejected CLI invocation). Passing semantic
checks:002,003,004,007,008.001 rejects unsupported --release before compilation;
subsequent builds say `[optimized]` and use opt-level3.005 and006 timed out at240s
while expanding dynamic reads from a57,607-byte symbolic array. They were replaced
with strictly smaller pointer+length identity obligations007/008, not rerun
unchanged and not given larger caps. Exact failed sources/logs remain committed.
On these timed-out process groups GNU time's RSS measures the surviving launcher,
not all descendants; the receipt's cgroup_memory_peak_bytes is the aggregate
memory evidence. Do not read the small timeout RSS as CBMC's memory footprint.

All attempts use the unchanged S2W_run_host.py inside individual6G high/8G max/
swap0/tasks64 scopes. No Kani stub, assume(canonical), symbolic oracle, validator
contract or source-success premise is used. Bounds assumptions only select the
actual loop domain. They are inhabited; the Lean audit gives a header+scan-success
fixture and rejects the original padding witness and a deployed-length version.

The source-to-reference association remains the pre-existing P6 trust boundary,
recorded here. The Lean theorem does not prove Charon/Aeneas/Kani/tool or ELF
correctness. D188's native association is retained at the new installed dictionary.
No new trust item, cryptographic assumption or release metric is introduced.
