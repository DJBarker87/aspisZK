# Slice-boundary findings

No new trust or callee success premise is introduced.

* F1: `r1_wire::ValidatedRecord::payload`, frozen r1_wire.rs:131–133, is the private range borrow called by decode_k147. It is absent from NFQ_SLICE_D. Existing decoder model/byte-range theorems and local CLOSED decoder status do not establish the missing caller/native payload carrier law. Requires lead-owned membership/packet resolution.
* F2: `aspis_core::r0::heap::uninit`, frozen r1_semantic.rs:45 and r0/heap.rs:11–22, is the custom Vec/Box allocation shim actually called by claims129. NFQ_SLICE_D lists heap::filled, not uninit. The inventory classifies the outer uninit(...).map_err expression as library/runtime/callback without a callee row. This shim is custom source, not silently a new trusted Std API. NHU initialization-flag proofs do not certify this shim or heap provenance/cleanup. Requires scope/packet resolution; no outside-slice proof attempted.
* F3: sampler::circle_sample156 calls secure_ood_circle_point_from_parameter and transcript::circle_fallback_point, neither in slice D. Closed Q inv/try_inv/neg/square packets remove the old field boundaries, but not these two source helpers. Singular/subfield branches and fallback cannot be assumed absent. Requires committed outside-slice packets and same-parameter/block domain instantiation.

All source inspection uses frozen4bb3b3f51e16b4525f1d10336e2b0bcbbd775387 and immutable Git objects. No sibling or session-A worktree is touched. A proposed scope repair is not an adopted packet or a CLOSED row.
