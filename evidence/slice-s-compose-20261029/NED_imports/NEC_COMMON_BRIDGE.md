# asq8_common conditional bridge

Claim NEC::asq8_common is CLOSED-CONDITIONAL on all typed input records, with the existing allocator/runtime/ABI/P6 physical interpretation retained. This is a local bridge input for NED; composed ledger rows remain OPEN.

Native source-to-reference: unchanged NDM safe common_ref and common_contract windows, 14 positive/control pairs listed in NEC_COMMON_REVALIDATION.json. Reconstruction from each committed patch matches all per-receipt Rust source hashes, and actual asq8_common body is byte-identical to frozen 4bb3b3f5. Exact deployed feature graph, frozen lock, KMX hash, successful proof and intended ensures failure are mechanically checked per pair. No Option<fn> data, field product, semantic callee stub or stub_verified is reached. NDM K029 timeout is excluded; its split value/frame successors K031–034 provide coverage without retrying the timed-out shape. Zero-master predecessors are excluded.

Extraction/cohort: reused NDM extraction pins and safe reference; NEC_L001 replays imports on copied/pinned objects and checks NEC_Common.reference_cohort against the SAME coherent adopted constructor. NEC_Common.windows_transport uses finite field/array extensionality for every common field. The native windows are universal over the SAME typed prestate domain; applying their P6 interpretations supplies its Fields premise. That native semantic transport is explicit owner-approved tool trust, not a Lean discharge of Kani soundness.

Caller domain: reconstruct_asq8_statement calls this after its step and asset gates; the constructor needs none of those restrictions. PacketDomain=True therefore adds no caller assumption. Heap liveness, Box allocation, ownership and source-to-ELF are retained physical interpretation, not claimed removed. No verified Box-return contract substitution is used.

Only new compile NEC_L001: exit0, wall2.5354059101082385s, peak2593484KiB, swap0. Exact revision/source/dependency pins and all three standard-only #print axioms results are in its receipt. No new Kani or extraction run; unchanged admitted predecessor results reused after static audit. No shipped file or ELF changed.
