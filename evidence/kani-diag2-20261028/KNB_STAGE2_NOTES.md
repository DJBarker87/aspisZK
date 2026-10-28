# Playback preparation

Setup copied (never moved or deleted) the read-only query cache into the owned persistent kdiag2 cache. Owned scratch source copied from the existing NBO scratch, then all K042-captured inputs restored, including Cargo.lock. KNB_native is a prefix-only rename of K042. Existing shared sources and caches were not edited.

Setup input correction: the first remote setup string contained an unescaped newline and failed at Python parsing, before writes. Corrected own input to use chr(10); second setup exit 0. This is rule 11 input correction, not a host infrastructure repair.

KNB_K001 requests concrete playback print with -Z concrete-playback in an optimized dev profile. The paired G001 metadata gate must pass and match the frozen graph before submission. Receipt source_revision is the current worktree commit; source snapshots/hashes identify the actual experimental source.

No causal conclusion yet. A passing native replay must substitute the mark stub explicitly: normal native compilation does not apply kani::stub. The native property must include the stub assertion, phase and call count; running the shipped mark alone would not reproduce this harness observation.

## Classification established

KNB_K002 reproduces K042 with the original NBZ harness: only obs.is_none fails (1/274), 3/4 covers, and concrete playback prints failure input i=2,k=3,j=63. KNB_K001 uses the prefix-renamed KNB body and passes (0/274), 4/4 covers. Native KNB_R001 replays all 533 primitive choices / 3176 bytes against actual carrier types and the explicitly substituted observer stub; all assertions and full input consumption pass under cargo test --release. Classification (b): false failure. This is not evidence of a shipped Rust defect. It does not yet attribute fault to KMX versus Kani/CBMC.

Own launcher-input correction: R001 initially collided with pre-existing G001 metadata receipt and stopped before scope submission. Changed Rust metadata namespace to GR001; the receipt and retry log are retained.
