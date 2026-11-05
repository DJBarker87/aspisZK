# NID local-record stub table

No multiplication, SHA, writable static, function-pointer assertion,
proof_for_contract or stub_verified. Exact KMX patch is retained:
bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67.
Inherited NHV/NHT/NFW stubs and paired laws remain pinned in NID_INPUT_PINS.json.

| Stub / cut | Paired model law and domain | Status |
| --- | --- | --- |
| ReadLog.read in one checkpoint weight iteration | CheckpointBytes3Reader.read_k_c5; T2Nat_ScalarJoin.k_eq / T2Nat_ReaderOps.readK. Same bytes1768, cursor712+16*i, i<64. Explicit Ok(K,next) or all eight Error variants; only LOCAL log updates. Caller property is universal in reply. | Native/model step composition and complete callee full-Result association remain OPEN. Arbitrary reply is not a callee certificate. |

Every selected family requires matched corruption and rename stability. Compiler
failures do not count as failing semantic controls. Native cut results do not
supply canonical decoder facts; NID_ResumeCanonical derives those on exact model
codec values. Runtime syscall aborts have abort-prefix/no-suffix boundaries (an),
not a fabricated Err arm.

| Additional local record | Exact paired law and domain | Status |
| --- | --- | --- |
| LeafLog.digest, three private-leaf grammars | Port4B_LeafCode.code_exact/address, newly composed NID_MerkleLeafPacket.selected. SAME source-selected opening832; tree0 tag0x71/value0..480/salt608..640; tree1 tag0xf1/value480..608/salt640..672; folded tag0x72/value672..800/salt800..832; prefix0x10. Arbitrary32-byte reply, one local call, unchanged reply. | K017–052 positive/control/rename. Only digest bytes and byte-slice association; SHA VALUE remains Runtime H. Complete parent batch_tree/verify packet still OPEN. |

NID_BoundedReaders.k/e upgrades the retained scalar EqOk to exact full Result
ONLY with the caller's actual in-bounds read. NID_BoundedReaders.weight/semantic
derive the bound from original checkpoint1768 and exact cursor712+16*i /408+16*i.
No global EqOk-to-equality coercion is admitted.

| Final window/copy operation | Named paired theorem | Exact domain / retained boundary |
| --- | --- | --- |
| RawWindowLog<J>.enter, J=0/1/2/3 | NID_RawWindowFrame.row/rows; NID_KmxComposition.copy_four_spec/copy_four_frame/rows_spec/all64/selected | Arbitrary SAME64-row raw vector, each4 u64, arbitrary row<64; one contiguous8-byte limb per native harness. K107–118. Four disjoint windows compose to KMX's indexed-copy value law and symbolic64-row induction. Native/source carrier association, valid pointers, non-overlap, allocation and ABI remain the existing caller/P6 domains. |
| Actual Reader.raw16/raw32 | T2Nat_RawJoin.reference, NID_RawOffsetCover.cover/unique | SAME checkpoint1768, all valid source offsets;32-byte source coverage is seven partitions. K053–089. Full native source is frozen, not a replacement raw reader. |
| Actual Reader.k | NID_BoundedReaders.k; CheckpointBytes3Reader.read_k_c5 | Full Result on all valid16-byte offsets K090–092; value facets on actual resume schedule K094–105. NID_KOffsetCover covers rho,10 semantic values,4 coordinates, power and64 weights. No claim for other native caller offset schedules. |
| Actual Reader.e | NID_BoundedReaders.e; CheckpointBytes3Reader.read_e_c5 | Ordinary Result predicate K119/K120 on all valid32-byte offsets; complete native value/source/caller packet still belongs to resume integration. No Observer/fn pointer, no stub_verified. |

The KMX source used by the value laws is byte-identical to the prescribed patch:
NID_KMX_VALUE_PIN.json records both patch and extracted Lean source hashes. New
copy composition is symbolic; no concrete256-cell recurrence is normalized.
No multiplication stub, new cryptographic assumption or digest-value model is
introduced. The complete actual op18/op5/op19 laws remain open.
