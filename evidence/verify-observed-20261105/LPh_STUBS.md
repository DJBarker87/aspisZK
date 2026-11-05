# NGX substitutions and paired laws

No field multiplication is run, stubbed or proved in Kani in this stage.
The exact prescribed KMX patch is applied, payload hashes checked before each
run, and every selected context has a matched failing control.

| Cut / stub | Paired law / CLOSED packet | Domain / modifies |
|---|---|---|
| OracleHash::digest | NGC_DigestBridge.forwarding + accepted P1/RuntimeSyscall; NGX_SampleTrace returned/rejected | SAME3/2/2 descriptors; immutable inputs; arbitrary reply32; local log only. Never SHA unwinding. |
| NewHash::digest | same NGC/P1 packet; NGX_NewTrace returned/rejected; SemanticRuntime domain_bytes/seed_domain | SAME5 descriptors, each<=57607; exact38-byte private domain, tag0, U32 LE length, original public/root; local log only. |
| validate_cut | CLOSED NFU validate_record_fields; NGX_ParseRecord.source / validator_domain | Every u8 row, payload<=3712, all bytes; full Error/Unit, no input mutation. |
| record_cut | NGX parse_record packet, installed after its admission | SAME framed5..3717; every Error, original payload on Ok; no input mutation. |
| KMX copy_nonoverlapping/copy_from_slice | exact KMX_CopyMeaning value laws and current paired controls | valid disjoint destination/source where required; only destination writes. No custom copy replacement. |

Descriptor identity is linked to the SAME admitted memory map by the existing
NGT_RuntimeDomain.same_descriptors/input_frame laws. Sparse payload fixture
bytes alone are never asserted to realize a full digest request. Native bodies
only forward these immutable descriptors; the full arbitrary-byte runtime
forwarding obligation is the accepted NGC packet, not sparse-window inference.


| Additional cut | Paired law / status | Domain / modifies |
|---|---|---|
| prefix_at_cut | CLOSED parse_record_at; PrefixSource.source / PrefixGeometry / PrefixCarrier | SAME live bytes<=57607, row0..26, exact derived offsets/widths; exact errors or original framed window/end; no input write or query. |
| semantic_block_cut | CLOSED sample_block_validated; SampleTrace and SemanticDomain.total | SAME token row<=24, framed<=3717; RowOrder or SAME atomic digest-derived read/final replies and cursor; same hash. |
| semantic_qm_cut | CLOSED qm31_sample; SamplerStages.sample / SamplerJoin.total, reused NGT_Reduction.K | SAME arbitrary block32, four SAME native remainder coordinates; canonicality is derived from the sampler, not an independent parent success premise. |
| begin_semantic_cut | OPEN caller association; NOT admitted as an actual semantic state law | Native control support only: all15 arguments/errors/outputs/state transport. Actual states/events must still be instantiated from semantic packet; no arbitrary next state is credited. |
