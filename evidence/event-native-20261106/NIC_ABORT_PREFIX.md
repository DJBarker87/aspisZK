# Native abort-prefix boundaries under ruling (an)

The abort boundary preserves the attempted failing call and all earlier occurrences, and has no suffix. It is not a recoverable Rust Err arm and asserts no totality or native divergence result.

| Boundary | Native positive / control | Exact scope |
|---|---|---|
| scalar digest absorb/read/advance | K032 PASS / K033 FAIL | arbitrary input state32, row<96, len<=2048, either mode, arbitrary stop index0..2 |
| scalar_k digest absorb/read/advance | K034 PASS / K035 FAIL | same input scope, every stop0..2 |
| query digests | K036 PASS / K037 FAIL | same input scope, every stop0..16 of the frozen eager digest-call sequence |
| constructor Box<Prepared> allocation cut | K046 PASS / K047 FAIL | actual Box::new at the typed Prepared boundary; canonical E/Q value fields and arbitrary remaining record fields |

The digest harnesses instantiate the unchanged generic frozen Transcript methods with a local-record Digest32 backend. Its returning branch returns arbitrary32; at the selected abort it sets the local stopped flag and executes kani::assume(false). This is the explicit nonreturning boundary licensed by (an)/RuntimeSyscall, NOT a proof that a physical syscall aborts. Returning controls remove termination and fail on a later digest or sampler/reduction sentinel. All logs/counters are local Cell records; there is no writable static. The positive cannot reach the samplers/reduction sentinels; they are unreachability assertions, not replacement value laws.

The Box positive replaces Box::new by a same-signature nonreturning boundary, and the control restores the real returning Box allocation and fails at the suffix sentinel. The actual constructor's returning value/ownership/allocation checks are inherited from NGN/NHS under (aa); this check does not re-prove them or assert a recoverable Error::Allocation for Box. The accepted allocator row supplies fresh unique ownership or abort. NGN's emitted endpoint erases allocation, so NIC_AbortPrefix.allocation_div exposes an explicit partial step; it is not falsely identified with an emitted allocation node.

Returning exact-byte/value/log evidence is REUSED from NGT_CallerInterface/NGT_BlockAssociation, NHK_Invocation/NHS_QueryFailures, and NGC_DigestBridge, with source/table/receipt hashes in NIC_REUSED_INPUTS.json. No passing returning shape is rerun. Generic backend substitution is the same source-parameter transport used by those packets; actual SolanaDigest realization remains RuntimeSyscall returningValue, with no totality.

NIC_AbortPrefix.read_fail/read_div retain the attempted call; allocation_div and NIC_AllocatorPrefix.fail/stopped retain prior events for both partial terminals; scalar_stopped reuses NIA's SAME BlockStop and proves arbitrary-context frames. Both model fail/div arms use those existing partial rows; no success premise is added. NIA_ConstructorTrace/ScalarFailures and NHZ's stopped-bind rules retain constructor predecessors and prevent later constructor events. Native physical parent installation/op9/ordering remains external.

All receipt commands use deployed features, frozen lock/graph before and after, exact KMX where copies are reached, optimized Rust, caps6G/8G/0/64 and no timeout increase. K029–031 were input/compiler failures and are excluded; see NIC_FAILING_STEP.md.
