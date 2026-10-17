# Attempt v5: full fast-encoder cut hit memory pressure

Source input SHA-256: `b8251cf30b7cb20ca933a037ac467f01d8d0ba342780222f7d6c1b8c462251c8`.
Toolchain: rustc `1.98.0-nightly (14210df0e27ccd7d9e6a05b8085cbd438e4bbc65)`,
Charon `daad69bea1114042a2d2fbd3dfde99922b152d4f57023bf8edb83e5a6f336af8`,
Aeneas `959659a6aafc6a6a975b4dc67ee9d779a269b988bd44b3b31a77cf023b1709e3`.

The release Rust compile and Charon translation succeeded. Aeneas translated
for about 29 seconds, then remained blocked in `mem_cgroup_handle_over_high`
at 6.4 GiB RSS with no output generated. The cgroup was
`MemoryHigh=6G`, `MemoryMax=8G`, `MemorySwapMax=0`, `TasksMax=128`; it recorded
9,797 high events, zero max/OOM/OOM-kill events, and zero swap. The process
was stopped cleanly rather than increasing the cap. Logs are retained in
`logs/`. This result reflects the expanded full encoder target and does not
show that a narrow digest-byte extraction is infeasible.
