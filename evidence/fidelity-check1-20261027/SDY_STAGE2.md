# Native stage

SDY_R002 passes three native tests covering twelve fixtures (three/function).
Frozen Rust 4bb3b3f51e16b4525f1d10336e2b0bcbbd775387; only scratch cfg(test) wrappers appended. Exact unmodified bodies and hashes retained as SDY_frozen_*.rs.txt / SDY_native_pins.json. Unchanged source files are symlinked read-only to retained source; only the three source overlays and lock are privately written. No shipped source changes.

cargo test --release --locked --offline -j4; CARGO_NET_OFFLINE=true.
Resolved packages checked against frozen Cargo.lock before each run; lock hash unchanged: 5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef. Graph and lock receipts retained. R001 failed for missing test-local std import; R002 adds extern crate std in each wrapper. Setup once failed before any Rust launch due missing scratch root directory; corrected before R001. No timeout/memory kill.

Multiproof uses a specified fixture Digest32: the first byte of the first child, repeated 32 times. This deliberately exposes restored children; it makes no cryptographic-backend assertion. The supplied 224 sibling bytes allow one eight-way level then rejection on missing second-level sibling. Full bool/idx/val output checked, not just acceptance. The native returned unit for row/finish is represented by the resulting mutable state; add additionally returns its carry Boolean. Exact fixture outputs in R002/stdout.log.

Private kit builds L001,L002,L004–L018 passed. L003 ordering preflight failed (missing SDY_Join_Field), before Lean launched; ordering corrected rather than launcher changed. All 17 kit sources exactly invert to XRn_Join_* by name replacement (SDY_kit_manifest.json). SInt2 cache reused read-only. No final release or whole-manifest replay claimed.
