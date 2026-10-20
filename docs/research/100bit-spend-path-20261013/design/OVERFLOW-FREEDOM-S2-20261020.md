# R22 stage-2 integer and bounds audit — 20 October 2026

Scope: frozen verifier `b2727acd3`, worktree base `8ced75478`, branch
`codex/cx-overflow-s2-20261020`. No verifier or existing Lean module is edited.
Packet paths below are relative to `docs/research/100bit-spend-path-20261013/`.

## Status and meaning

R22 remains OPEN. This packet distinguishes checked-operation range proofs,
actual self-contained emitted-function totality, and unproved backend/caller
composition. An ordinary `ok (.Err e)` is allowed; Aeneas `fail` or `div` is
not total execution. Successful-execution inversion is insufficient.

The generated input is
`evidence/stage2-continuation-20261020/generated/AspisR1Stage2/Funs.lean`
(abbreviated **F** below). Its import at F:5 names `AspisR1Stage2.FunsExternal`,
which is absent from that generated directory. Thus importing the complete
emission does not supply concrete field, codec, pairing, iterator or allocation
semantics. This is a proof-input boundary, not evidence that Rust overflows.
`Stage2ContinuationQueryAdvance.lean:8` and
`Stage2ContinuationResumeBody.lean:6` instead expose typed operations. Arbitrary
such operations can fail; their totality cannot be concluded from canonical
field limbs alone.

The freeze's `FREEZE.md:40` and `llbc-comparison.json` establish that frozen
LLBC `f11e40b4…` and predecessor LLBC `4c36344e…` have identical bodies after
normalizing only destination and short-name ordering. The generated bodies in
this audit are the committed predecessor emission, not a newly run translator.

## Premises that must be carried, rather than inferred from success

Let P=2147483647, C=(P-1)^2, B=2^34, W=Usize.max. Parsed/sampled M31
limbs must be <P, all live field kernels must preserve this, and leaf indices
must be <2^18. Rust `as`/`UScalar.cast` is total truncation, not a checked cast.
Checked add/sub/mul, shift counts and indexing require the bounds below.

The three headline invariants in the task do not alone imply per-helper
totality. Also needed: framed slice sizes/cursors; 0≤w≤i<n≤16 for Merkle
frontiers; bounded slot and query positions; start≤next and geometry vector
lengths; weight/raw vector agreement; basis width≤256; mutable residue phase
invariants; and total backend/observer operations. These are explicit premises,
not additions to the deployed input format. An out-of-range direct helper call
is not automatically an admitted tx2 input.

## Inventory

The machine-readable `operation-census.json` gives every lexical local scalar,
cast and array/slice/vector access site in F, by function and line. It is not a
verified call graph. The tables below include transitive/library obligations
that a lexical operator search cannot establish. Usize bounds fit even a
32-bit target. Iterators additionally require length/remaining-range invariants.

### Compact framing and binary multiproofs

| Function (F line) | Types and failure-capable operations | Sufficient invariant / safe bound |
|---|---|---|
| compact constants (156–381) | Usize +, -, * | Semantic values 426; logical bytes 13831; compact semantic 7015; offsets Y1=7031, inactive=7495, round0=7527, folded root=7751, round1=7783, final=8007, openings=10055; opening=832; nodes=28359; max nodes=914; proof=57607. All intermediate operands/results fit U32. |
| candidate.opening (264) | Usize i*832, 10055+product, end+832; range index | i<22, proof.length≥28359; end≤28359. |
| slot_offset_loop/body/slot_offset (302–331), candidate.slot (334) | table[i], Usize 32*count, cursor+, i+1; slot+1; range index | slot≤6 for offset, slot<6 for slice; i<slot, cursor=28359+32*sum prior counts; prefix sum≤914; end≤57607. |
| parse_shape (436) | proof[..8], proof[8], proof[9..16]; byte comparison/iteration | proof.length=57607 from guard; literal ranges valid; comparison and iterator contracts still required. |
| batch_keys_loop/body/batch_keys (476–523) | Usize lo+j; queries[lo+j]; U32 /4; U64 <<8; cast j→U64; keys[j] | n≤12≤16, lo+n≤22, j<n; query<2^18; key <2^26, low-byte j<16; shift8<64, divisor4≠0. |
| batch_key_at, sort_batch_keys loops (525–600) | keys[index]; Usize j-1; swap indexes via backend | index<16; sort length≤16; j>0 before j-1; comparisons do not change lengths. |
| batch_leaf (603), same_batch_leaf/index (651/661) | opening slices [0..480],[480..608],[608..640],[640..672],[672..800],[800..832]; idx/val[index] | opening length832; tree<3; index<16. Hash/backend equality totality separate. |
| index_at/value_at/root_matches (717–737) | array[variable], val[0] | variable<16; fixed root read always valid. |
| sibling_binary_parent (675), occupied_binary_parent (699) | values[index]; Usize index+1; values[index+1] | sibling: index<16; occupied: index+1<16; digest total on three slices. |
| well_formed and closures (747–864) | U32 1<<18; pair-window[0],[1]; iterator | 18<32; windows have length2, callbacks total; length guard 1..16; index bound <2^18 and strict increase. |
| Arity.bits/levels/width (867,875,1230) | U32 18/bits; Usize 1<<bits | bits∈{1,3}; levels∈{18,6}; width∈{2,8}; nonzero division and valid shift counts. |
| verify_in_place inner binary loop (1006) | U32 index>>bits; Usize i+1,i+2,w+1,at+32; idx/val updates[w] | w≤i<n≤16; paired branch i+1<n; w<16; at=32*consumed; consumed≤914 (attempted end≤29280). Failed slice.get returns false ordinarily. Successful read is within nodes. |
| verify_in_place octal inner loop (883) | U32 >>3, mask7 cast→Usize; i+1,at+32; enumerate/update | slot<8, i<n≤16; same cursor budget; hash eight children. Stage-2 caller uses Two, but emitted generic branch is inventoried. |
| verify_in_place outer loops/wrapper (1130–1226) | iterator advancement, nodes.length%32; prefix/slice copies | initial idx/val n≤16, node bytes multiple32, levels≤18; each level maintains w≤n and cursor budget. Shrinking frontier invariant must be proved, not inferred from final verification. |
| node_count loops/wrapper (1238–1375) | U32 >>bits; Usize j+1,j-i,width-(j-i),count+,w+1; level[w]; prefix copies | sorted distinct frontier; i<j≤n≤16; each parent group size≤width (critical subtraction premise); count≤914; w≤i. Sorting/distinctness must survive in-place compression. |
| batch_tree_loop/body/batch_tree (1431–1564) | key_position+1; U64 >>8; casts to U32/Usize; lo+lowbyte; d-1; idx/val[d]; d+1; SLOT_NODES[s]; 32*count; slot slices; hi-lo; 3*batch+tree | key_position<n≤12; sorted packed keys; d≤key_position≤n, insert d<n≤16; d>0 before previous lookup; lo≤hi≤22; batch<2,tree<3 so s<6; count≤SLOT_NODES[s]≤172; node slice length≥32*count, slot padding extends to fixed size. |
| batch_merkle_values/batch_merkle (1569/1613) | roots[0..2], p.roots[0..1] | fixed arrays 3 and2; batch children retain contracts above. |

914 is the sum of six reserved slot capacities (146,146,128,172,172,150),
not the maximum number of entries in one frontier (16), nor the loop count
for every traversal. Conflating these bounds invalidates array-index proofs.

### Query accumulation, resume and final relation

| Function (F line) | Types / sites | Sufficient invariant / safe bound |
|---|---|---|
| accumulated_weight_at/basis_at/power_limb_at/residue_limb_at (1626–1652) | Slice/Array indexes | index<weights.length; basis index<256; lane<4. |
| update_residue_row loops/wrapper (1655–1744), BatchedWeights.push (1748) | U32→U64 widening; U64 power*basis, old+product; four-lane update; U64 >>31 and (limb&P)+high; Vec mutable index | canonical power,basis gives product≤C; old<B+(terms%4)*C; next≤B+4C<2^64; fold of any U64 is <B; lane<4, index<raw.length; phase and fold cadence mandatory. |
| accumulate basis inner/outer loops (1764–1830) | basis[j], basis[n+j], n*2; M31 mul; range iterator | width∈{64,256}; n successive powers of2, n<width; j<n, n+j<2*n≤width≤256; doubled n≤256. |
| accumulate weight loop (1833–1872) | i*width+j; one rho push; basis/weight selection | actual body uses i from a.next (0..21), j<width, width≤256; flattened trace position<22*256=5632; data accesses use j, so raw and weight vectors both require width rows. Raw phase bound above is essential. |
| accumulate_batched_with_node (1878) | basis[0]; terms+1; a.next+1; WideExact/K mul/add | terms≤21, next≤21 for an active query; raw width matches a.weights; canonical values and field outputs. Merely knowing node<2^18 does not bound either counter. |
| line_fold_with_inverses (1906), circle_fold_with_inverses (1948) | inverse[2..4]/[0..1], values[0..3]; field/WideExact kernels | fixed five/four-element arrays; canonical inputs and preservation by every child field operation. Zero inverse values are representable; algebraic nonzero-denominator conditions concern correctness, not scalar overflow. |
| QueryGeometry.for_query (1988) | index-start; inverse Vec index | start≤index; index-start<inverses.length. |
| query_values closure (2008), candidate.query_values (2058) | slice[672..800]; weights.field indexes; queries[next]; U32→Usize cast; 4*next+0..3,2*next+0..1; u%4; alpha[0,1]; values[u%4]; next-start; line_z Vec index | opening832; j<4 for closure field reads; next<22; trace positions≤87/43; modulo divisor4 nonzero; remainder<4; start≤next and geometry lengths>next-start; canonical kernels; child errors may reject normally. Actual emitted name query_values denotes the complete query, unlike the small source closure with the same prefix. |
| query_loop/body (2120–2181) | compare next<end; query child; finite Aeneas loop | next starts10, end22; child increments next by1 and terms by1 preserving all ranges, or returns ordinary Err. Existing stage2_twelve_ordered_calls is successful-execution inversion, not this totality statement. |
| Reader.raw/k/e (2246/2260/2485) | Usize at+N; bytes[at..end]; fixed-array conversion and unwrap; field parser | at+N≤bytes.length≤W; N=4/16/32; exact slice length=N makes unwrap safe; k/e may reject noncanonical bytes ordinarily. |
| read_checkpoint_semantic_alpha/weights and loops (2273–2431) | Reader.k/raw and iterator/vector update | ten alpha entries; weights.length=final_len∈{64,256}; cursor advances exactly16 per K; enough checkpoint bytes reserved before final digest. |
| validate_checkpoint_queries loop/body (2435–2481) | queries[i]; U32 1<<18; i+1; duplicate search iterator | i<22, successor≤22; shift18<32; q<2^18 validated or ordinary Checkpoint rejection. |
| CHECKPOINT_FIXED/checkpoint_size (2500/2547), Variant.folds/final_len (2527/2538) | Usize constants+,*,1024>>(2*folds); fixed+16*length | fixed744; folds1/2; shift2/4; final_len256/64; checkpoint4840/1768. |
| resume (2556) | bytes[..8],[8],[9],[10],[11..16],[16..48],[48..80],[len-32..],[..len-32]; Reader sequence; header U8→Usize cast; query/weight decoders | exact-size guard4840/1768 precedes all indexing/subtraction; header next≤22; reader starts80 and ends len-32 after exact fixed fields, ten alpha entries and final_len weights. Digest/byte comparisons, allocation and decoder totality still separate. Canonicality follows only on ordinary Ok of strict decoders. |
| finish_query_dot_loop/body/wrapper (3044–3105) | weights[j], weights.field(final_message,j), j+1; EbyKDot push/finish | j<weights.length=final_len≤256; final_message.length=32*final_len; field limbs canonical; dot push count≤256<4096; accumulator ranges as stage-1 raw bound lemmas, linked to this backend. |
| polynomial/closure (3110–3171) | reverse iterator0..7; weights.field(i); WideExact mul/add | i<7, bytes.length≥224, canonical seven coefficients and x; Horner intermediates canonical. |
| finish_relation_round (3178) | fields[0,4]; Usize 3*round,+1,+2; WideExact add/mul_m31 and polynomial | round∈{0,1}, trace≤5; poly≥224 canonical bytes; QUARTER canonical; claim/alpha canonical. |
| finish_relation (3208) | alpha[0/1], prefix alpha[..folds]; weights.new/pair; dot; callbacks | folds∈{1,2}, two alpha entries; final_message length32*final_len; all weights/pair domains from stage-1 inventory required; fixed array reads safe. Pairing is an external boundary, not proved by the final equality comparison. |
| BatchedWeights.value/finish (3336–3436) | raw Vec row; lanes[0..3]; reducer calls; out Vec update through iterator | index<raw.length=weights.length≤256; reducer total even for unrestricted U64; output canonical; output vector same length. Stage-1 value proof is for a different emitted type and needs transport to this body. |
| BatchedWeights.new/loop (3442–3494) | weights[index]; U32→U64; raw mutable index; index+1 | index<weights.length≤256; allocation returns a vector of that length or ordinary Err; initial raw lanes canonical (<P), terms=0. |
| batch_prefix_products (3722–3762) | flat[index], index+1, field mul; Vec push | flat.length≤110, index<length; product canonical; allocation/Vec push semantics separate. |
| QueryGeometry.for_range closures/loops/wrapper (3504–3720,3768–3987) | flattened 5*i+k; flat/prefix Vec indexes; query cast; u/4,4*(u/4)+3; end-start;(end-start)*5; scalar kernels, Vec push/collect | start≤end≤22, query<2^18; count≤22, flat length5*count≤110; i<count,k<5; 4*(query/4)+3<2^18; inverse batch arrays and reverse scan lengths must agree. |
| tx2_common/authenticated (3993/4112) | proof[..7031],[7031..7495],[7527..7751],[7783..8007],[8007..10055]; children | parse_shape's exact57607 bytes guard dominates slices; resume yields next10 checked before the loop; geometry built for 10..22. Canonical output/content, observer, allocation, multiproof and finish contracts must compose. |

Field-leaf arithmetic is unchanged in kind from stage 1: canonical U32
add≤2P-2; offset subtract uses self+P≤2P-1 and rhs<P; U64 products≤C;
CM31 cross product≤(2P-2)^2<2^64; shifts31/32 are below64; reducer's first
fold≤10737418238 and second≤P+4. See stage-1 inventory sections3/6 and
`R22FastPairingRawRanges.lean` for ordered private raw expressions. These
facts do not by themselves instantiate opaque stage-2 operations.

## Findings and stopped targets

No overflow on an admitted complete tx2 input has been established. This is
not an all-input overflow-freedom theorem.

The stronger target “each helper is total from canonical parsed fields,
indices<2^18 and counts≤914 alone” is false. Concrete counterexamples:

- F:2250: Reader.raw with cursor=W and N=1 computes W+1 before any slice
  check. Its byte slice may be empty; all field/index/count restrictions are
  vacuous. The corrected statement needs cursor+N≤bytes.length. This is a
  direct-helper counterexample, not a reachable tx2 counterexample.
- F:1671: old=2^64−1, power=1, basis=1 computes old+1 in U64. Both field
  operands are canonical and a node index of1 is legal. The mutable old-lane
  phase invariant is indispensable; this state is not shown reachable from
  BatchedWeights.new.
- F:1992: index=0,start=1 underflows before the Vec read, regardless of
  canonicality. Geometry.for_range and ordered query progress must establish
  start≤index. Again this is not a reachable-input finding.

These unrestricted-helper targets are stopped and replaced by the explicit
range contracts above. No verifier change is proposed.

The direct Reader.raw theorem initially compiled, but its axiom report
included `core.fmt.Formatter`, inherited from
`core.result.Result.unwrap core.fmt.DebugTryFromSliceError` (F:2257).
That receipt is **rejected**, despite exit 0. The replacement reader theorem
abstracts only unwrap as a function argument and assumes its behavior on Ok;
its axiom audit is standard-only. It does not claim concrete Reader.raw
refinement. No existing Aeneas/Lean module or cached object was rewritten.

## Proven scope and remaining composition

`R22Stage2LocalBodies.lean` retains 31 verbatim emitted leaf definitions
without generator attributes/options (body hashes and line pins in the packet).
`R22Stage2LeafTotal.lean` proves checked add/mul/sub equality helpers,
19 concrete layout/size results, and the two actual 16-entry index accessors.
It computes layout constants bottom-up through named checked-operation facts;
no large recurrence, finite-field universe, or unbounded reduction is evaluated.

`R22Stage2ControlBounds.lean` proves 13 symbolic control/index bounds and
checked scalar totality facts, reusing the stage-1 sampler byte-index lemma.
These are range lemmas, not source-function totality claims.
`R22Stage2ReaderTotal.lean` proves the unwrap-parametric raw reader total
from its byte-end bound (including N=0), preserving its cursor and byte slice.
`R22Stage2OpeningTotal.lean` targets the complete actual opening accessor.
The final accepted targets and axiom reports are indexed in the manifest.

Still required to close the requested per-function proof, and therefore R22:

1. Supply standard-axiom concrete definitions/contracts for the missing
   FunsExternal dependencies, including codec, field/tower arithmetic,
   private fast pairing, fast_dots, iterators, array construction, vector
   allocation/mutation, observers/traces and debug-bearing unwrap. Link the
   stage-1 arithmetic theorems by actual body/type correspondence.
2. Prove sorted distinct frontier and budget invariants through the actual
   in-place multiproof loops, node_count, batch sorting/deduplication and all
   six slot prefixes; compose ordinary rejection paths as total checked runs.
3. Prove checkpoint read sequencing/field parser totality and all allocation,
   semantic-alpha, query and weight decoding loops. Discharge cursor and
   vector-size premises from the exact-size guards.
4. Prove the actual geometry and residue phase invariants, basis and weight
   loops, query child totality and progress for 10..22, both fold equations,
   pairing and final-value loop. Canonicality must propagate bottom-up, rather
   than be assumed only at the final checked acceptance.
5. Compose authenticated entry→resume→Merkle→12 queries→finish with these
   contracts, then run the project's single final frozen manifest replay.

No full regression, Rust/SBF rebuild, new extraction, or release-completeness
claim is made by this packet. Existing modules and verifier source are intact.
