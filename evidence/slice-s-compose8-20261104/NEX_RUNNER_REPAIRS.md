Setup initially requested unused S2W_lean_host.py from predecessor; it does not exist. Removed this own-input mistake. No prover launched; reservation admitted. The existing S2W_run_host.py is the actual unchanged launcher and remains hash-pinned.

NEX_L001 excluded: audit module referenced the encoder theorem without importing its module. Removed that unrelated reference, retained the successful printed predecessor axioms, and added targeted decoder-definition inspection; changed-source L002 passed. NEX_K001 excluded: an extra comma in the generated digest-oracle call caused a compile error; fixed the generator. K002 was the first common whole-field shape and timed out; K003 split to field0, passing with four matched controls. The frozen graph, features, KMX checks and resource limits were unchanged.

K051 excluded own-input error: nested Rust mod resolution required an explicit #[path="NEX_exact.rs"] for the scratch sibling file. Added it to the exact/afterdecode/snapshotdecode generators and strict exact checker; no frozen body changed.

The own validator falsely treated AtomicStatementError as an atomic-storage type. Exempted that exact required enum name, retaining all former Atomic-storage rejections and adding whitespace-robust static-mut and Cell/RefCell/UnsafeCell rejection. This does not allow writable statics; the capped preflight gate also independently scans declarations.

K132 excluded compile error: the generic statement projection returned withdrawal amount as u32 in a u64 function. Added the lossless u64 cast, matching the other raw scalar projections. Frozen terminal body and tested property are unchanged; no proof verdict was obtained from K132.

K134 failed harness selection before solving: the campaign supplied an extra crate prefix. Fixed only the owned campaign qualification, retained the original harness name and assertions, and scheduled K135..140 for six window checks. K134 receives no proof credit and still consumes one attempt.
