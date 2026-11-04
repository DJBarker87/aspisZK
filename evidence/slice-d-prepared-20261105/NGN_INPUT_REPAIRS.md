# Own-input repairs

K001 stopped in offline metadata because the scratch source archive omitted frozen c3/build and c3/check path dependencies. Added the original frozen paths, with archive hashes recorded.
K002 passed graph validation but Rust compilation stopped because the original statement module includes tools/r1-builder-reference/tree.rs. Added that frozen directory, with archive hash recorded.
K003 passed graph validation but Rust compilation stopped because exact KMX_stubs.rs requires allocator_api. Added cfg(kani)-only feature(allocator_api) to the scratch crate root. No KMX source changed. K004 then passed the unchanged gamma property. No timeout or memory-killed shape was replayed. These are worker-owned input repairs, not launcher/infrastructure changes.

NGN_run.py is a private adaptation of NGJ_run.py; NGN_gate.py adapts NFW_gate.py. Shared reservation, launcher, walker and build workspaces are unchanged. The gate retains frozen-lock before/after hashes, offline --locked metadata, complete package/edge comparison and deployed feature receipts. cargo-kani receives no --locked argument. All source/harness inputs remain committed as snapshots or patch, with the original frozen revision and archive hashes pinned.
