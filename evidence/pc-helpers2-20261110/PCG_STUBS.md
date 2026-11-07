> SUSPENDED NATIVE CONTEXT SUPPORT: PCG-F1 / PCG_FINDINGS.md. Do not consume the SDK/address/digest packets until repaired receipts replace their support. Logical Lean results are unaffected.

# PCG stub and domain register

No field multiplication stub, writable-static oracle, function-pointer oracle or borrowed stub_verified is used. No PDA value law or new runtime row is added. SDK op38 reply values remain quantified; coherent digest/error slots are op43/op44.

| Replacement | Paired Lean/source law | Domain and controls |
|---|---|---|
| SDK sol_create_program_address -> create_oracle | PCG_SdkPda.create_packet / create_reject / createReply; PCG_SDK_SOURCE.json source-ordered tail identity | Same seed descriptors/count, same program pointer, caller-owned32-byte output; valid seeds count<=16 and each<=32 at call. Actual zero/one step K019/002, arbitrary-count tail K020/021, arbitrary current seed length step K022/023, unsupported statuses K028/029. Status0 returns exact address;1/2 map exact errors;>2 abort. Invalid seed admission rejects before syscall. |
| SDK sol_try_find_program_address -> find_oracle | PCG_SdkPda.tryFindReply / findReply / find_forward / find_ok | Same descriptor/count/program, exact output/bump; K003/004 includes arbitrary u64 status; K024/025 actual find success; K026/027 actual find abort on nonzero. |
| Exact KMX copy_nonoverlapping | KMX_CopyMeaning loop_spec/copy_frame, inherited canonical library objects | Copy stubs are byte-identical to KMX_copy_stubs.patch SHA256 bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67. Every selected SDK pair uses the same ptr-copy configuration and negative control. No substitute copy model invented. |

The oracle context is a local repr(C) record. Its first field is the arbitrary program key; only the syscall stub accesses the remaining harness-owned fields through that field's same-allocation provenance. Calls are counted in a local Cell, never a static. Seed pointer/count checks precede reply writes. The actual wrapper sees only its ordinary arguments. Native caller composition uses this local-record convention; it does not add harness metadata to runtime account state.

P6/D188 native semantic transport and ReviewedTranscription PCG-RT-SdkPda are option-A reclassifications. Compiler, ABI, std slice/iterator and pointer/copy realization remain explicit retained trust. The source segment differs from the frozen SDK tail only by resolving its crate re-export path and the numeric SUCCESS constant; PCG_sdk_source.py rejects four meaningful mutations against the lock-checksummed registry archive.
