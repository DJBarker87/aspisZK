# Frozen stage-2 extraction inventory

This is an inventory/decision packet, not a closure of R14. See
[the report](../evidence/stage2-extraction-20261020/REPORT.md) and its checked
manifest. The verifier remains frozen at 9a71031d3.

## Exact source cut

`pins/cone.json` gives byte/line spans and SHA256 for 76 declarations and
16 closures. The count is explicitly bounded at named arithmetic, allocation,
stdlib, hash and account backends; it is not a count of every compiler-generated
trait implementation or monomorphization. See `backend_frontiers`,
`external_frontiers`, `stdlib_frontiers` and `excluded` in that file.

The stage-2-only declarations are `candidate::tx2_authenticated`,
`candidate::tx2_common`, `resume`, `Reader` and its three methods,
`finish_relation`, `polynomial`, and adapter `stage2` (10). All other listed
source declarations are also reached by the adopted tx1/checkpoint path.
The 66 shared declarations and 10 shared closures are source sharing, not an
accepted-extraction count. Only six listed declarations exactly match the old
accepted tx1 kit's fragments; matching other arithmetic packets is outside
that precise baseline comparison.

The source call order is:

1. Adapter `stage2`: seven accounts and request magic; clear return data;
   `validate_asq8`; borrow proof/checkpoint; checked proof extent and exact
   account length; statement serialization and its exact length;
   `verifier::tx2_authenticated`; `emit_result`. AccountInfo/RefCell guards,
   validator, encoder, SolanaDigest, observer and error conversion are external
   boundaries. This packet does not extract the SDK or prove Pool custody.
2. `tx2_authenticated`: `parse_shape`; `mark(Parsed)`; `tx2_common`.
3. `tx2_common`: `resume`; `a.next == SPLIT` guard; `powers::<29>`;
   `mark(CheckpointRead)`; `wide_view`; `batch_merkle(...,1,...)`;
   `mark(Merkle(SPLIT))`; geometry for `[a.next,22)`; batched weights;
   query-values loop while `a.next < 22`; pending finish; `finish_relation`.
4. `batch_merkle`: trees C1, C2, folded, in that order. For each, compute
   keys for queries 10..22, insertion-sort, hash leaves, reject inconsistent
   duplicate folded leaves, compute `node_count(Two,...)`, check slot padding,
   then `verify_in_place(Two,...)`. Stage 2 uses fixed slots 3,4,5.
5. `query_values`: opening access; fast four dots; circle fold and selected
   folded-value equality; line fold; accumulation. `accumulate_with_node`
   updates weights/rhs/power and increments `a.next` exactly once. The
   multiproofs precede the query loop; there is no per-query Merkle call.
6. `finish_relation`: fold guards and Horner update (S2 has two rounds),
   `Weights::new`, pairing and equality, Relation observer, final E-by-K dot,
   `a.next==22` and dot/rhs equality, Final observer.

Successful source execution processes 12 queries (indices 10..21), whereas
rejection may process only a prefix or fail before any query. A formal count
must prove actual loop progress, successful calls and early-exit behavior;
constants and successful fixture traces do not supply that proof. Binary
multiproof node/hash counts depend on indices and duplicates and are separate
from the 12 opening-arithmetic iterations.

The source closure ledger includes header/padding predicates, query-values
`from_fn`, resume's header predicate/mutable Reader capture/allocation mapping,
geometry's callbacks, polynomial's Rev.fold callback, finish error mapping
and adapter serialization error mapping. Implicit derive/iterator/Box/Vec
operations are listed as boundaries rather than silently counted as extracted.

`canonical_scan`, compact decode/expand routines, prover multiproof generation,
standalone `multiproof::verify`, `sort_dedup`, and the eight-way audit entry
are outside authenticated-stage-2 reachability. `verify_in_place` still has an
Arity::Eight branch syntactically: extraction cannot erase it solely because
this caller passes Two without supplying a specialization argument/proof.

## Blocker and proposed source decision

The exact frozen `finish_relation` body is SHA256
`11d1e3f65f5413fddf417578f582dc1f005a5d9de6db77c306a5e8540baebe38`.
It already failed with the **required** stage-1 Charon/driver/extended-static
Aeneas hashes, in a capped High6G/Max8G/Swap0 scope. This is sufficient to stop
whole-cone emission with that unchanged pipeline. The corrected-opacity caller
and corrected-layout resume diagnostic attempts also remain failed; those used
a later diagnostic tool hash and are labelled separately in the manifest.
None is a Lean proof or a fresh execution in this packet.

A concrete, unadopted proposal already exists at
[finish-relation-source-candidate-20261019](../lean-candidates/finish-relation-source-candidate-20261019/README.md)
with `verifier-candidate.patch`: factor each fold guard into a shallow scalar
helper, specialize the one/two rounds, and factor the final dot into an indexed
helper over shared slices. It is the smallest **retained successful finish
candidate**, not a proven minimal equivalent production change. Its candidate
proofs do not imply frozen-source equivalence. Earlier failed helper/index
variants and tool-only diagnostics are retained in the frontier packets.

No sufficient minimal source change is established for the entire cone:
`resume` mutable Reader/from_fn closure and post-finish Accumulator borrowing
need separate solutions. A scalar round/dot refactor alone is insufficient.
Do not adopt a helper-only copy into a synthetic extraction crate and label it
the frozen source. Any adoption changes verifier source, reopens R13/R12
re-pins and the CU bound, and requires codec 1,233 / ordered trace / checkpoint
byte-identity gates. A new authorized tool solution could instead preserve the
source. This packet stops for the lead's decision without editing Rust.

## Existing facts and remaining obligations

The base already contains partial packets missed by the earlier gap-map row:

- `evidence/stage2-authenticated-wrapper-20261019/`: actual wrapper success,
  universally over parser/common-call boundaries.
- `evidence/stage2-parse-variant-tag-20261019/` and
  `stage2-authenticated-parser-join-20261020/`: generated parser returns S2
  (tag 2), and wrapper/parser composition. Slice operations remain boundaries.
- `evidence/stage2-reader-cursor-decoder-20261019/`: raw/e/k success and
  checked cursor updates, over explicit decoder/unwrap boundaries.
- `evidence/stage2-resume-fixed-prefix-20261019/`: a manually isolated prefix
  adapter, not a generated whole-resume theorem. Later prefix-canonicality
  packets still require whole-caller reachability.

Their manifests and README scopes are hash-pinned in this packet. No theorem
is newly compiled, strengthened, or claimed to instantiate their boundaries.

The requested next actual-source facts are still obligations:

1. **Compact length:** successful authenticated entry implies proof length
   57,607. The Rust guard checks length, magic, S2 and zero header tail;
   `parse_shape` alone does not parse/canonical-scan every field. Join the
   actual slice backend and generated parser/entry bodies. No replacement
   handwritten Lean length predicate is introduced here.
2. **Rehash:** successful whole `resume` implies `bytes[16..48]` equals
   `H.digest(&[proof])`, with exactly the compact stored proof bytes (including
   padding), plus public digest/checksum guards. Short-circuit failures and
   actual digest-call ordering matter. This is binding to a supplied digest,
   not checkpoint authenticity or collision resistance. Reader-prefix proofs
   do not derive this whole-resume success statement.
3. **Query structure:** derive entry at 10, exactly ordered C1/C2/folded
   multiproof successes, query arithmetic at 10..21, and terminal next=22;
   prove the rejected-input prefix bound separately. Hand-isolated tail
   candidates do not prove reachability from the frozen common caller.

R13/R12 remain source/model/Checks refinements, including concrete arithmetic
and Merkle backends. R15 remains authenticated checkpoint provenance and
canonicality of values skipped by `tx2_authenticated`. R19 remains the
all-input hash/first-read bound, joined through R10's global digest log;
12 iterations are not a complete oracle-call bound. R9/R20 still join the same
statement/proof/checkpoint bytes through the Pool and adapter. Whole R14 and
100-bit soundness remain open.
