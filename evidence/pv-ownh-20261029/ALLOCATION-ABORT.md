# Fixed requests and retained failure behavior

For both roots, successful source execution issues the same requests:

1. Allocate127 Links (size8/alignment2):1016 bytes.
2. Filter in place to64 Links, retain capacity127. Reserve190 additional slots;
   amortized capacity is max(2*127,64+190)=254. Reallocate1016 ->2032 bytes,
   alignment2. Appends end with136 initialized Links. No pointer determines
   the counts or branch selecting this request.
3. Flatten exactly136 two-word endpoint arrays to272 u16s. The nested collector
   allocates544 bytes/alignment2. It does not need further growth.
4. Release the2032-byte Link allocation after its source iteration is exhausted.
   Sort and adjacent dedup do not allocate;214 live words remain, capacity272.
5. V229 returns this544-byte Vec to the caller. The caller owns its eventual
   deallocation. V230 consumes it into64 masks and releases544 bytes before
   returning. The stack masks and sort scratch do not create heap requests.

These facts follow from the unchanged constructors/reserve/collector source,
fixed lengths and the address/source argument in STATIC-CHECK.md. The named
`request_layouts` theorem composes the existing first_public, second_public and
third_public laws. CollectorProgram.complete and MasksWorld.complete retain
all allocator outcomes and post-states in the model. They are supporting
resource laws; this task does not claim an own-1 byte-memory instance.

If the first/second/third request fails, the successful trace stops at that
prefix and the actual1016/2032/544-byte failure handler is invoked. The global
allocator may fail or diverge; diagnostic hooks, allocation abort behavior,
resource/runtime adequacy and the witness-independence requirement for the
public failure event remain explicitly under **rdea-1**. No assumption of
allocation success is silently inserted into the privacy endpoint. No mutable
panic/diagnostic read is reclassified as a pure caller-memory operation.
The no-input/address-independent ordinary computation makes each request
prefix fixed; it does not prove allocator-state privacy or OS adequacy.

The previous instrumented differential in
`../pv-rdb2d-20261028/rdb2d-forest-native/output.log` is supporting finite
validation only. Its retained log demonstrates successful request traces and
fail-at1/2 injections; this task does not upgrade that log to a deployed
allocator proof or claim an additional fail-at3 execution. The D439 harness
uses the ordinary default allocator and no instrumentation. V370/D381/D386
still covers codegen/runtime primitives; T is unchanged.
