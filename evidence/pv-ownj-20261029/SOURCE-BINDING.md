# D449 consuming source binding and influence analysis

Classification: partial structural binding under own-1. This is not a complete
V239 source/decoder/ownership refinement. Source-to-codegen remains V370 and
D381/D386; allocation/null/abort and runtime adequacy remain rdea-1. Existing
Aeneas/Rust agreement is reclassification within existing tool trust.
`source-binding.json` pins exact source spans and checks ordered stage tokens.

## Dense value obligation

The inherited raw value law is unconditional on raw four-limb inputs. Its
operations are CT profile wrapping source operations, not a Field instance.
A decoder homomorphism cannot simply be asserted on every raw limb pattern:
wrapping u32 addition has a different modulus from M31. Canonicality must be
proved for the actual consuming columns, generated weights, and points, then
transport must use the canonical arithmetic laws for these exact raw bodies.
The new Decoder structure states these obligations on explicit limb bounds;
it is a conditional local interface, not an endpoint assumption discharge.

Rows are `pref*2^trailing+suffix` in increasing prefix order. The row decoder
is quotient/remainder by `2^trailing`; the scanner suffix consists precisely
of literal ZERO/ONE elements from the reverse takeWhile. The native suffix
shift/OR encoding and bounded row law are inherited. Connecting this concrete
range enumeration to the Fin-function dense sum remains part of the value
join until an actual decoder and row-transport theorem is compiled.

## point_claims (:749–760)

The outer iterator is exactly `wire::statement_points(point)`. The returned
order is point, successor, xor12. Successor starts as a point copy and visits
coordinates9..0; at each coordinate it computes `bit.mul(carry)`, then
`bit.add(carry).sub(product.add(product))`, then updates carry. It overwrites
every slot and never reads an overwritten successor slot. xor12 copies the
input and subtracts coordinates7 then6 from ONE; these independent stores
are represented by the new map's tests6/7, with no allocation/destructor
between the two stores. The three fixed arrays have length10.

The inner iterator visits columns0..28 in order. Its first call with a length
other than1024 returns None before sparse allocation, maps to Error::Public,
and propagates through `?`; neither later lanes nor later points are visited.
The Lean claims model erases only this unique Error::Public tag to None.
A source binding to an Option model is not an extracted complete Rust Result
refinement; successful allocation failures retain their separate world effects.

At the consuming builder :792–808, c1 lengths are checked before commitments;
each is1024. The helper's Vec is converted to &[QM31;1024] before use and its
shape-error stop precedes column construction. g/d already have array type.
At :826–831, lanes0–25 are length-preserving lifts, then26=h1,27=g,28=d are
1024-element copies. Thus column lengths are [1024;29] at every reached call,
independent of values. Incorrect input lengths stop earlier, not inside this
instance. Generic point_claims still retains every first shape-error stop.

## Callback :879 and final alpha :890

The source query constructor is state_only_hiding.rs:1587–1627. Initially all
coordinates are zero. At round r, coordinates<r retain previous semantic
challenges. The sample loop overwrites coordinate r with the fixed lift of
sample0..27. The assignment loop overwrites every coordinate>r with its
fixed Boolean assignment. Therefore each query is
`alpha.take r ++ [lift sample] ++ assignmentBits(9-r, assignment)`.
The current round's oracle values, initial_claim, running and interpolated
polynomial never enter the point stores. They affect boundary checks and the
framed polynomial; the polynomial is then passed to transcript.semantic.
After successful semantic, that exact frame is appended to output before
any query of the next round. Thus every preceding challenge used by a query
has its source frame in the published prefix at that moment. The terminal
callback uses exactly the ten sampled challenges. The caller receives this
same point as alpha and uses it at :890.

The seed is hash(DOMAIN,0,le32(public_bytes.len),public_bytes,C1root). C1root is
the first32 published bytes. Rows0/1 are empty, row2 carries C2root, rows3–13
are empty, row14 carries the published mask sum, rows15–24 the published
polynomials. The scalar closure appends each exact frame after successful
semantic and before later scalar/query work. Each sample_block checks order
and parses before hashing, computes absorbed=H(state,0,0xa0+row,frame),
block=H(absorbed,1), state'=H(absorbed,2), then increments next_row. semantic
maps block through the fixed qm31_sample. No rejection-sampling retry or
unpublished polynomial message is used to derive a point.

The new FiatShamir model computes this recurrence explicitly from public
bytes, published root and frames, with fixed hash and sampler functions. It
is not a theorem just accepting alpha as an argument. It models successful
validated frames; parser/error and byte-carrier source refinement remain
separate. Existing TranscriptR1 documents this exact three-read pattern;
ProverCommitEffectCallers27.semantic_call proves its effect-threaded extracted
helper, and ProverRwFullSemantic.from_read connects the current sampler to
its actual read block. Those existing laws are supporting references here,
not imported/recompiled whole-consumer discharges.

No unpublished influence on the callback point or final alpha was found in
this source analysis. This does not establish witness-independent occurrence
of an entire failed prover execution: boundary/oracle errors and resource
failure positions must still be accounted for by the complete consumer law.
