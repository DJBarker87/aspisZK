# Pool helper packet index

All24 packets are candidates until the final combined gate. Each negative receipt must fail the intended assertion (or SDK missing-panic property), not compilation or unwind. Frozen graph, all-crate feature lists, KMX hashes, lock-before/after and exact source hashes are per attempt. No field multiplication or runtime SHA evaluation in Kani.

| Pool row | Root | Native positives | Failing controls |
|---|---|---|---|
|POOL:159|PCG_ErrorLaws.receipt|K052|K009|
|POOL:160|PCG_ErrorLaws.account|K010|K011|
|POOL:181|PCG_OwnedTree.row_181|K063|K056|
|POOL:184|PCG_MarkerCodec.row_184|K064|K065|
|POOL:186|PCG_CanonicalLaws.row_186|K057|K058|
|POOL:189|PCG_ErrorLaws.forest|K012|K013|
|POOL:241|PCG_PageLaws.row_241|K099|K100|
|POOL:242|PCG_PageLaws.row_242|K048|K049|
|POOL:287|PCG_ConversionLaws.row_287|K014|K015|
|POOL:288|PCG_ConversionLaws.row_288|K016|K017|
|POOL:293|PCG_PackComposition.row_293|K076 K078 K080|K077 K079 K081|
|POOL:296|PCG_MarkerSeed.row_296|K101 K095|K094 K096|
|POOL:318|PCG_MasterAddress.row_318|K086|K087|
|POOL:323|PCG_CheckpointAddress.row_323|K084|K085|
|POOL:324|PCG_GlobalLaw.row_324|K072|K073|
|POOL:345|PCG_ReturnBridge.row_345|K066 K068 K070|K067 K069 K071|
|POOL:368|PCG_DigestBridge.row_368|K088|K089|
|POOL:374|PCG_AddressRoots.row_374|K084|K085|
|POOL:375|PCG_AddressRoots.row_375|K084|K085|
|POOL:376|PCG_AddressRoots.row_376|K084|K085|
|POOL:377|PCG_AddressRoots.row_377|K084|K085|
|POOL:379|PCG_AddressRoots.row_379|K097|K098|
|POOL:390|PCG_AddressRoots.row_390|K084|K085|
|POOL:391|PCG_AddressRoots.row_391|K084|K085|

SDK replacement: K092/K083 each cover the same eight original harnesses, with Miri L057 provenance repair. K084/K085 each cover stored_matches and all seven address requests; final379 uses the broader independent-descriptor K097/K098 pair. Old PCG-F1 context receipts are excluded, even where earlier reports said pass.

Native324 uses one exact seven-call local log and arbitrary canonical replies, composed with NJZ_TreeParent.source at every SAME left/right. K074 whole-function diagnostic timed out and is excluded; it was not retried. Native345 forwards the owned Option reply, retaining Vec pointer/length/capacity and arbitrary selected byte; its source has no payload reads/writes. Native296 has actual-argument diagnostic K101/K094 and arbitrary full child-reply log K095/K096. Exact source-fission erasure for324/345/296 is PCG_ASSOCIATIONS.json.

Packing293 uses K076/077 word step, K078/079 one write/frame, K080/081 group association; PCG_PackLaw.read_suffix and PCG_PackComposition.chunk_induction compose the loops. PCG_LOOP_ASSOCIATION.json pins the frozen loop skeleton. No whole-digest Kani loop or concrete large Lean normalization.

The all-root raw walk is authoritative under(ab')(3); collector disagreements, if any, stay recorded. Existing eight fixtures use the same unchanged binary. Full scope metrics and source revisions are in PCG_ATTEMPTS.jsonl and each receipt.
