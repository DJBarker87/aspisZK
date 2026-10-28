# NBM finding: K050 generated playback does not fail natively

**Classification (c). Native execution does NOT fail the same assertion on the K050 trace. Stop bridge credit under the explicit first-task ruling.**

This is a pinned Kani-verification/native-playback discrepancy in the standalone slice-copy harness. It is not a shipped `node_count` counterexample, a universal compiler-bug proof, or a proof of the exact internal tool defect. `multiproof`, `keys`, `batch`, TX2 U09 and S2 remain OPEN. No headline premise is removed.

## Exact comparison

The generated test in NBJ_K050/stdout.log is copied verbatim, including every byte vector and the call to `kani::concrete_playback_run`. The K050 harness body and its `#[kani::unwind(2)]` annotation are verbatim too. Only the containing module is named NBM_copy; two alloc imports make the generated test compile in the frozen no_std crate. The precise fixture is input[7]=1, input[15]=512, every other input word=0, n=16, k=15. It satisfies the standalone harness's n/k assumptions. It fails the real node_count strict-order guard, so there is no reached-source node_count bug claim.

K050's original verification fails an assertion: 1/47 checks failed, 4 unreachable. Its generator was explicitly enabled by `-Z concrete-playback --concrete-playback print`; K049 was excluded. We reuse this generated artifact, not R001's handwritten reconstruction.

NBM_R003 runs that generated test through pinned `cargo-kani playback -Z concrete-playback --lib -- --exact multiproof::NBM_copy::kani_concrete_playback_NBJ_count_copy_prefix_8053088788365222636 --nocapture`. The output states:

```
Finished `test` profile [optimized]
running 1 test
test multiproof::NBM_copy::kani_concrete_playback_NBJ_count_copy_prefix_8053088788365222636 ... ok
test result: ok. 1 passed; 0 failed; 0 ignored; 0 measured; 16 filtered out
```

The SAME assertion is `assert_eq!(level[k],if k<n{input[k]}else{0})` after `level[..n].copy_from_slice(&input[..n])` into a zeroed 16-word array. Native playback therefore passes the expected value 512 on the selected index; no replacement assertion or independently supplied final array occurs. This rules out (a) an incorrect expected-value assertion and (b) R001 being the sole differently constructed comparison. Classification (c) concerns the observed verification result versus native execution; the precise internal cause remains to be isolated.

## Validation actually run

- NBM_R001: compile error, missing explicit module path; no test execution. Exit1, wall199.571354524s, peak RSS587668KiB, swap0.
- NBM_R002: compile error, generated Vec/vec imports missing in no_std module; no test execution. Exit1, wall1.356460902s, RSS185844KiB, swap0.
- NBM_R003: generated native test PASS. Exit0, wall25.239490744s, RSS239576KiB, swap0. Source revision98dbd1b1a4f63167598cd98a91c576a597515247 plus exact dirty source hashes in receipt.json.

Each invocation validates all selected dependency package identities and edges against the frozen lock before execution:441 selected/444 frozen, no new package or unmatched edge; offline. Every after-run lock hash equals before:
`5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef`.

Each uses a separate admitted scope, MemoryHigh6G/MemoryMax8G/MemorySwapMax0/TasksMax64. Native test/dev profiles opt-level3, debug0, overflow checks on. No timeout, memory kill, raised cap or parallel scope. No new Lean theorem: axioms N/A. Own scratch-hook/import fixes leave the generated test and assertion unchanged; no infrastructure fix.

## Minimal reproducer and limits

`NBM_copy.rs.txt` contains one three-input copy harness and Kani's generated test. `NBM_playback.patch` installs only its cfg(kani) module in a scratch projection of frozen Rust4bb3b3f51e16b4525f1d10336e2b0bcbbd775387. It needs no digest, field stub, protocol loop or cryptographic input. Use the frozen Cargo.lock, offline graph validation, and the pinned Kani0.67.0 playback command above with the recorded optimization profiles. The original failing verification is NBJ_K050; an NBM minimal diagnostic regeneration is recorded separately. No bridge theorem may cite this copy gate as passing.
