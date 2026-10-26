# P6 source certificate: shipped Claims to selected owned reference

Scope: the frozen `r1_semantic.rs::claims` on an actual successfully parsed Claims prefix. This is a local source-helper refinement and its installation in the existing accepted-pair cone, not global S2 or a 100-bit release result. Earlier stage reports correctly had delta zero while this composition was incomplete.

## Source and extraction binding

`NP6_start.json` pins the untouched shipped source and original joint theorem at baseline `30c4fd3eba3bdad6ea5cab8152abe14a4c21a234`. The complete Claims function in `NP6_claims/src/NP6_shipped.rs` is byte-identical to the shipped function. The complete wire/sampler are retained; only the wire's cfg(kani) constructor exposes its otherwise private record array. It makes all records refer to the arbitrary record, without modifying any called method. All 87 core Rust files match the retained host source (`NP6_core-validation.json`). No source stub, `kani::assume`, allocator substitution, decoder replacement, or canonicality restriction appears in an accepted gate.

The owned reference is exactly the already extracted run10 `candidate_claims.rs`, hash `c45a50413e98be523eb27cf7a2ea54929791b1f85b66320abbd5985e53db94db`; an unchanged copy is `NP6_reference_origin.rs`. It allocates three zero rows with filled, transfers through into_boxed_slice/try_into, then performs the three real decodes and setters. `NP6_check.py` checks both complete function bodies, not just their names. The selected Aeneas source is the existing ClaimsUnrolledParentSource/Rows/Finish closure reused from the coherent SInt2 workspace. No new extraction, compiler modification or safe-reference implementation is substituted for that candidate. The existing `ClaimsUnrolledFinish.claims_value` bridge and the new reference normalization are the value-model connection.

The arbitrary Kani frame has **3717 bytes**, the actual row25 size (header5 +116*32). All bytes are unrestricted, including noncanonical limbs and all unused high halves. The earlier 2789-byte whole-body attempts were not accepted certificates. `NP6_RecordShape.on_parsed_prefix` and `NP6_ParsedClaims.on_success` derive this width from the SAME accepted parse and actual source getter, rather than postulating it. The Claims function only accesses record25 and does not inspect the root or other records; the frame constructor therefore covers every helper invocation at this source cut. Rejected outer parses never reach this helper; their original prefix accounting is retained.

## Full Result and complete buffer contents

The successful gates execute each COMPLETE, literal native or reference caller, including actual allocation, getter, decoder loops, early errors and drops:

| Gates | Universally checked fact |
|---|---|
| K017/K018 | On Ok, each of all87 fields and4 limbs is the corresponding original input u32, below P=2147483647. The selected original low word is unchanged on every Result. |
| K019/K021 | Every Err in the returning-allocation profile is exactly NonCanonical{row:25,value:bad}, bad<87, with at least one noncanonical limb at bad. |
| K020/K022 | On that Err, every limb of every field before bad was canonical in the ORIGINAL input. |
| K023/K024 | Every one of all3717 original bytes is unchanged on every Result; result ownership is explicitly dropped. |
| K029/K030 | The full caller and explicit drop also satisfy CBMC memory-leak and memory-cleanup properties on every returning branch. |

The arbitrary selector ranges are exhaustive: u8%87, u8%4 and u16%3717 all cover their entire index sets. No success assumption appears. In particular, error payloads are compared by their first invalid field, not by a common error tag alone.

`NP6_ScalarResult.unique` proves that the returned values or first failing field characterized by these six unary facts are unique. `NP6_FlatExt.injective` proves that all348 raw scalar fields determine the EXACT Claims carrier. `NP6_ResultBridge.complete_result` then proves exact equality of the full Result, including NonCanonical's row and Usize payload and the complete boxed value. Its hypotheses are the concrete unary properties checked above, not equality between caller outputs. This is a split Kani certificate composed by a kernel-checked mathematical proof; no successful monolithic relational Kani run is claimed.

K013/K014/K015 independently compare the actual pointer/write/decode expression against the real safe setter for each of the three positions, with arbitrary prior initialized rows and arbitrary record bytes. Every Result and every initialized-prefix cell is compared; K015 also performs the actual assume_init conversion. `NP6_Initialization.complete` proves symbolically that the three writes initialize every row independently of prior memory. The literal source performs no typed Claims read before those writes, and reaches assume_init only after all three decodes/writes succeed. Optional Kani uninit instrumentation was unavailable (K005 compiler ICE); that optional instrumentation is not represented as passing evidence.

## Ownership, effects and the allocator boundary

K025 uses actual std and heap operations. It checks QM31/row/Claims sizes and alignment, native and reference equal allocation Layout (1392 bytes, alignment4), capacities1 and3 respectively, no shrinking allocation during either boxing transfer, address preservation through ownership transfers and native assume_init, arbitrary native payloads and safe zero-filled contents. Both Claims and MaybeUninit<Claims> have no element Drop. The native expression and safe expression therefore issue the same one requested allocation before decoding; ownership stays private, returns in the one Box on success and is released on error. K029/K030 check release in the actual full callers, rather than relying on output equality for cleanup.

The binding native Vec/Box ruling is applied exactly: safe extracted standard-container behavior uses D188's standard model; the unsafe caller uses these P6 gates; allocator returning behavior stays under the EXISTING Allocator item. The fixed nonzero Layout cannot fail from capacity overflow. On a refused allocation, both literal helper/control prefixes map the same reserve error to Allocation BEFORE decoding or pointer writes. `NP6_StdBridge.allocation_failure` proves the selected complete safe reference's error branch, and `map_error` identifies the literal emitted Result::map_err. This is conditioned on the shared allocator outcome; it is not a claim that the Kani Rust allocator verified arbitrary allocator implementations or that allocation always succeeds.

K026 confirms that merely enabling CBMC malloc failure does not make Rust's reserve fail: its failed-allocation cover is unreachable. K027/K028 are excluded diagnostics: even a custom always-null GlobalAlloc with a dispatch counter is not called by this Kani profile. They are not counterexamples against shipped Claims, not allocation-failure coverage, and not extra trust. Raw failures remain retained. No infrastructure or allocator compiler model was changed to force a favorable result.

The observable frame here comprises original immutable record bytes, exact Result, every live output byte, and private ownership/allocation/cleanup. Claims has no hash, oracle, logging or randomness call. Equality is modulo private allocation addresses; it does not assert equality of inaccessible dead heap bytes (the safe buffer's unwritten suffix is zero, the native suffix is uninitialized on early rejection). No error branch exposes those bytes, and neither type has a payload destructor. Both source expressions use the same decoder order and preserve outer rejection/abort conditions. Existing runtime/entry/ABI and allocator assumptions remain explicit; no new ambient-state trust is introduced.

## Safe slots and same-run installation

`NP6_StdModel.calls reservation` is the standard safe owned interpretation: reserve preserves vector contents for either outcome; intoBox returns the same contents. Its successful and failed-return laws are proved, not supplied by a caller. The allocator response remains explicit, rather than a successful-child premise. `NP6_ClaimsModel` proves filled contents using the actual row Clone identity and normalizes the COMPLETE selected safe reference, including failures. `NP6_StdBridge.box_array_contents` proves the successful Box-array content law.

`NP6_ParsedPair.accepted_pair_unified` is the prefix-only strengthened installation of `T2Nat_NativePair.accepted_pair_unified`. It fixes the Claims std dictionary to those safe slots and retains every original joint premise and conclusion. On the SAME source cuts, accepted parse, semantic prefix, Claims result and TX1 run it additionally derives:

- initial weights=64 zero coefficients, rhs=0, power=1, next=0 and interpreted initial accumulator;
- pending rows equal the mapped initial weights, terms=0 and length64;
- all three actual Claims decoder equations at offsets0,29,58, exact returned row contents, actual source record length3717 and the same successful parse.

No independently successful child call, selected replacement run, assumed Claims contents, native equality premise, or new cryptographic premise is added. D188 associates this selected reference dictionary with the extracted stages; P6 supplies the shipped-unsafe/reference correspondence above. The old free-slot theorem remains byte-identical and available for other selections. Prefix-only scope means adoption of the strengthened module by the lead is a separate repository integration step, not a rewrite of another owner's module.

## Non-vacuity, conditioning and limits

R002 is an optimized native fixture: the REAL Prefix::parse accepts13831 bytes; row25 is3717 bytes and both complete callers return all87 distinct nonzero QM31 values identically. This is fixture evidence, not an exhaustive proof or an accepted cryptographic spend. K006 also reaches both full-box success and third-row rejection. `NP6_Constructors.local_nonvacuity` gives returning initial/pending values; its axioms are standard. No impossible premise was introduced by the joint strengthening.

Content conclusions are explicitly conditioned on original accepted native wrappers and reached successful semantic/constructor calls. Full helper error Results within the reached parsed-prefix domain are covered by the unary certificate. The original outer fail/diverge, rejected-prefix, source cuts, hash/runtime, crypto and other cone premises remain. The certificate does not prove a global security bound, freeze a new release, or reproduce the three ELF pins.
