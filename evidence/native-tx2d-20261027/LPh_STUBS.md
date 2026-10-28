# NBH local callee-replacement ledger

This file is inside the assigned NBH evidence directory; the shared LPh ledger is untouched. No field multiplication is executed or replaced in this job.

| Native callee / replacement | Named Lean return theorem | Exact domain | Caller establishes |
|---|---|---|---|
| pair_tree_profile::digest_is_canonical → NBH_digest (arbitrary Boolean constrained to all eight raw limb bounds) | NBD_DigestInduction.source; NBD_DigestInduction.same_scanner for account variant; native child NBD_K006 / NBD_DigestNativeStep.source / NBD_DigestTrace.native_result | Every eight-u32 Digest, including noncanonical limbs; exact Boolean iff each limb<P | Typed root/frontier field is exactly eight raw u32s. Level<20 before row access; zero initialization and preserved bound in NBH frontier induction. No canonicality assumption is imposed. |

The NBH probes spell the callee replacement explicitly at the source cut; no extra `kani::stub` attribute, stub_verified contract or trusted equality is introduced. NBH_NATIVE_PROBES.json retains exact frozen windows and transformations. NBH_STUBS.md gives the complete composition scope.

Store/prefix windows take an explicit already-returned32-byte argument and do not execute or fabricate encode_digest_canonical success. Those caller bridges are OPEN at NBH_Dep_DigestEncode; arbitrary bytes in a window are not a passing unpaired encoder stub. Payment/late encoders likewise retain their explicit lower/member dependencies. K024/K025's full dynamic stores timed out and have no pass credit.
