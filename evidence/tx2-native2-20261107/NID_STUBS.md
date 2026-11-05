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
