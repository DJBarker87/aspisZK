# Checkpoint native bridge plan and status

All assigned members OPEN in this worker; zero closure credit. No Kani, Rust, extraction or Lean launch. Read-only source hashes match frozen4bb3b3f5 for the seven release inputs checked (NGC_SOURCE_REVIEW.json). No cfg(kani) change in shipped files; no three-ELF rebuild trigger.

| Member | Exact required packet | Current disposition |
|---|---|---|
| CM31::write_le_bytes | Actual two four-byte copies, raw limb LE bytes, SAME out prefix/frame, length>=8; KMX exact patch and matched failing copy/value control | OPEN; host disk stop before scratch/cache preparation |
| QM31::write_le_bytes | Exact two CM31 calls on out[0..8] and out[8..16], arguments, ordered mutation/frame and callee domains; matched control; Lean substitution | OPEN; independent caller source review done, child certificates absent |
| heap::filled | Actual reserve/Allocation error, SAME Vec ownership, length/value/frame and resize iteration; specialize reached Copy instantiations, not a fake infallible allocator | OPEN; host disk stop |
| Accumulator::new | Exact final_len argument and ZERO passed to filled, Allocation mapping, rhs ZERO/power ONE/next0 on success; full Result and frame; SAME returned allocation | OPEN; filled child open; final_len is already CLOSED |
| SolanaDigest::digest | Actual hashv argument slice-of-slices passed unchanged, reply returned unchanged as [u8;32], one chronological digest event and frame | OPEN; independent of field writers; host disk stop |
| checkpoint | One arbitrary-prestate native window/transition with invariant; KMX controls; Lean 116-transition composition and all child domains; exact post-finish incoming domain | OPEN; NGC_DOMAIN.md lists separate preparation/write-back joins |

Digest trust is the RETAINED RuntimeSyscall/P1 hash-return realization (sha256=H) and the existing source/library/ABI/P6-D188 option-A transport. Prove wrapper byte slices/reply/order; never unwind SHA. RuntimePersistence is retained across transactions. RuntimeReturnData(nonempty1..1024) and RuntimeMemcmp are accepted but do not discharge digest forwarding or checkpoint writes. No new runtime row is used or proposed.

KNE_Leaf.native_result, KNE_Final.schedule_facts and KNE_Composition.compose are reusable candidates by citation within their exact domains: 115 body appends, then checksum; length1736 before checksum,1768 after. They retain LocalCorrect native schedule, actual trace, three chronological digest calls, Oracle, and WriterDomain premises. None proves its own caller domain or replaces a native one-window packet. No unchanged failed KNE shape launched. No XRn join used.

New proof roots must appear alongside RPx_Deployed.deployed in NGC_COMBINED_IMPORT, then pass NFX scan and raw ax2 driver/fixtures before a row is admitted. Present combined file is an uncompiled baseline template, with no NGC theorem and no claim of audit success.
