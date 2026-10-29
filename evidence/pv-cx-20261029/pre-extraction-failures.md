# Changed-input retries before MIR extraction

N73300 (exit 101): own staging omitted path dependency z4. Added exact baseline
z4 and c3 archives, no edits to any archived file. N73301 (exit 101): own staging
also omitted refine/blockwriters (and adjacent writers/poseidon). Added those
exact baseline directories. Both failures precede Rust type checking/extraction.

N73302 (exit 101): proc-macro2 build-script link fails with LLVM std::system_error
"Resource temporarily unavailable" under TasksMax=64. N73303 adds taskset 0–3
and historical RUSTFLAGS=-C link-arg=-Wl,--threads=4. This is a changed compilation
input, not an unchanged retry or a cap increase. Release/locked/offline/features,
source and extractor unchanged. Reuses the same job-owned target directory.

All four IDs count against the 30-run ceiling conservatively. No Lean attempts.

N73303 (exit 101, 171.156 s): compiler reaches aspis-statement, then discovers
another omitted baseline file, refine/diffharness/tests/glue_gen.rs at
pair_forest_copy_builder.rs:223. N73304 adds the entire small refine tree and
three explicit research #[path] modules identified by a git grep over frozen
source. These are unchanged git bytes; source-manifest verification checks all
staged inputs, not just the executable files. The compile cache is reused.
