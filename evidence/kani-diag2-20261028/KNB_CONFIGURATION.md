# Configuration comparison, stage 1

Compared the immutable per-attempt source snapshots retrieved from the host, not the current shared scratch source. Fetch completed with exit 0. Full snapshots and prefix-normalized diff are retained here.

| Setting | NBW_K026 | NBZ_K042 |
|---|---|---|
| Receipt source revision (dirty) | f84b1eed957b8d6d4e6c9176162a24f9ecd67549 | 14860f4d09e2daefcf2a8db3978f1d5b6adad3a3 |
| Frozen dependency revision | 4bb3b3f51e16b4525f1d10336e2b0bcbbd775387 | same |
| Kani | 0.67.0 | 0.67.0 |
| Unwind attribute | 4096 | 4096 |
| Solver flag | absent (default; executable identity not captured historically) | same |
| Kani flags | --lib -j 1 -Z unstable-options -Z stubbing --harness-timeout 90s --exact --output-format terse | same |
| Harness | verifier::candidate::NBW_native::NBW_return_carriers | prefix renamed NBZ |
| Result | 0/274 failures, 4/4 covers | 1/274 failures, 3/4 covers |

The complete first 1229 lines of the normalized native harness source are identical; NBZ appends negative controls. In particular the positive return-carrier harness and its mark stub are identical modulo prefix. verifier.rs, lib.rs and KMX_stubs.rs are byte-identical. candidate.rs adds three module declarations (NBZ_native, NBZ_windows, NBZ_steps); full diff retained.

Both apply six KMX replacements: core::ptr::copy_nonoverlapping, [u8]::copy_from_slice, [u8]::clone_from_slice, [u8]::to_vec, Vec<u8>::extend_from_slice, alloc::alloc::realloc. The seventh replacement is verifier::mark -> PREFIX_mark_none. Stub source SHA256 ad8efb63d8ff791274c91eff9ccc5b9fb126f5a3ac7f27aa811ca11b8e25c138. No stub implementation difference explains the historical result difference.

Both receipts validate the same resolved graph SHA256 bb23b60cafd193e8149a16472d04d19832ef6aec4c9eac78c4e5827ff9fa9f48 and lock SHA256 5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef, unchanged after execution. Both use CARGO_NET_OFFLINE=true, CARGO_BUILD_JOBS=1, DEV_OPT_LEVEL=3, DEV_DEBUG=0, RELEASE_OVERFLOW_CHECKS=true and RUSTFLAGS=-C link-arg=-Wl,--threads=1; TMPDIR/manifest/target paths differ by job prefix. Host scopes match 6G/8G/no swap/64 tasks. See original receipts for absolute paths and metrics.

Classification and causal attribution remain pending concrete playback. Historical receipts do not record solver binary hash; a claim of exact historical binary identity would exceed the evidence.
