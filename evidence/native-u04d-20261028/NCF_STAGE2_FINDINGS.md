# Stage 2 limits and corrections

NCF_K010–019: native wrong-length checks on symbolic valid allocation lengths,
one arbitrary byte at an arbitrary offset; remaining payload bytes are zero.
The matched inverted assertions fail. This has no upper bounded length beyond
Rust's valid slice/allocator layout domain and Kani's existing memory admission,
but does NOT alone cover all arbitrary payloads simultaneously. Payload-havoc
contract candidates are prepared separately and get no credit before controls.

NCF_K020/K021: selected native std enumerate/nth write, little-endian window,
arbitrary pre-state and coordinate frame; positive passes and control fails in
the exact KMX configuration. This is a one-write fragment using nth selection;
it is NOT yet the original decoder's iterator prestate/next association.

NCF_K022/K023: EXCLUDED from source-correspondence credit. Own copied checkpoint
candidate used 262144 in BOTH step and oracle; frozen source uses 1048576.
Their pass/failure is retained as candidate evidence only. Correction uses the
actual native named constant, and independently pinned 1048576 in its oracle.
This source change permits a fresh attempt; no timeout/kill/rerun is involved.

The SSH client for batch11 stalled after submission; it was terminated locally
without signalling remote proof processes. Read-only recovery collected the
existing batch, which was never resubmitted. No host runner was edited.
