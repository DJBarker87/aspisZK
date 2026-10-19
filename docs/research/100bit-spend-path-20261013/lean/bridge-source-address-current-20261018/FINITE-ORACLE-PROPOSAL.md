`ExtractedSourceDigestOracle.lean` is a proof-only construction, checked in C's
focused source-trace workspace: exit0,3.217seconds,15standard-only axioms
reports. The exact accepted source hash is
`06a9e026a14e3c46f66330664ae6f3ebeedc6f07eff3db5cea919bf551f31901`.
The producing archive and full receipts are being packaged by C. It changes
no Rust, transcript transition, sampler, field, `sigma`, or `decodeState`.
Its sole project import is the checked `ExtractedSourceDigestAddresses` leaf.
The grammar covers semantic initialization and semantic/circle calls. It does
not claim an interpretation of the separate four-slice opening absorb calls.

The input syntax contains one fixed initializer, the actual three-slice
absorb layout, and the actual two-slice read layout. For two such inputs with
equal flattened address bytes, the draft proves equality of the entire
`Slice (Slice U8)` supplied to D. Absorb and read inputs recover their32-byte
state and fixed-width tag slice; mapped bytes recover the actual U8 slice
through the already checked encode/decode inverse. Read length33 differs from
absorb length at least34 and init length at least75. Init byte32 is84, while
absorb byte32 is0. Both initializer cases use the same actual initializer.

A total function on the existing finite `Addr L` space then chooses an input
with matching bytes, invokes the actual D at its exact grouping and fixed
generic hash, and decodes that returned state. The default0 branch handles
unmatched addresses or failing/diverging dictionary calls. The proposed
`oracle_at` theorem proves that these defaults cannot affect an actual
successful reached call. It uses exact grouped-input equality, rather than
assuming D hashes concatenations independently of grouping.

`trace_hashes` derives the fixed dictionary hash from source carry.
`trace_functional` supplies all three actual dictionary equations for the
same reached `SourceFull25.Call` list without a `DigestAt` premise.
`public_oracle` starts from actual public helper success and derives its
serializer vector, fixed hash and initializer oracle equation. Public length
and bytes remain actual constructor/serializer outputs.

The focused check reused the two current address/frame leaves and their
existing exact dependency closure. The rejected first input is retained; the
only proof fix was bounded natural-number association, with no cap increase.
This construction alone
will not establish a distribution on this oracle, collision exclusion,
recovered table context, or C1/C2 word custody. Those stay separate in C's
actual-trace/table composition.
