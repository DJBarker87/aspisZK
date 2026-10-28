# KDX Kani fidelity diagnostic

**KANI-MODEL — divergence persists with adequate unwind.** Diagnostic only: no bridge, opaque-leaf closure, premise removal, or release-security claim. Internal root cause is not established. The deployed headline and narrowed D188 trust boundary are unchanged.

## Mechanism

Pinned cargo-kani 0.67.0 / CBMC 6.8.0, frozen release Rust `4bb3b3f51e16b4525f1d10336e2b0bcbbd775387`, frozen lock `5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef`. Every invocation validates selected package identities and edges against that lock before Kani, offline, and checks the lock hash afterwards. Original NBM native playback is reused; no additional native result is claimed.

- KDX_K001: same arbitrary prefix-copy law with `#[kani::unwind(17)]`: FAIL, 1/47 checks, 4 unreachable.
- KDX_K002: no unwind attribute, `--default-unwind 17`: FAIL, same counts.
- KDX_K003: original `#[kani::unwind(2)]`, regular verbose reporting: FAIL, same counts.
- KDX_K004: fixed K050 fixture, original unwind 2, independent assertions on all 16 cells: FAIL at cell 15.
- KDX_K005: same fixture with old/raw CBMC output and `--trace --no-slice-formula`: exact post-copy values retained in `KDX_TRACE_VALUES.json` and full trace in `KDX_K005/stdout.log`. CBMC calls builtin memcpy with **n=64 bytes**. After memcpy, `[0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0]`; native NBM_R003 gives the same vector except cell15=512. Input[15]=512 is explicitly present before memcpy in this trace. This is not evidence that every cell after the second is unwritten.

Default unwinding checks are **enabled**: no `--no-unwinding-checks`, `--no-default-checks`, or equivalent is in the original K050/NBM_K001 commands or these diagnostics. Verbose KDX commands show CBMC `--unwind 2` / `--unwind 17` and no disabling flag. **No unwinding-assertion check is emitted** in the 47-check reports, despite the enabled setting; memcpy is a builtin model here, not an observed bounded copy loop. `KDX_K001_CHECKS.txt` through `KDX_K004_CHECKS.txt` retain full check lists and statuses; `KDX_CHECK_AUDIT.json` records exact CBMC commands. Original K050/NBM_K001 used `--output-format terse`, so their historical receipts contain only the summary, not a recoverable full list. KDX_K003 supplies the same harness body/attribute with detailed reporting and a namespaced module; it does not retroactively supply missing historical output. All 47 checks in KDX_K003: 42 SUCCESS, 4 UNREACHABLE, one FAILURE (`core::panicking::assert_failed_inner.assertion.2`).

The original cargo command is recorded in `evidence/native-tx1c-20261027/NBJ_K050/stdout.log` and `evidence/native-tx1d-20261027/NBM_K001/stdout.log`: `kani --lib -j 1 -Z unstable-options --harness-timeout 90s --exact --harness <copy harness> --output-format terse -Z concrete-playback --concrete-playback print`, with the recorded absolute manifest and target directory. Unwind2 is the source attribute, not a CLI flag.

## Exposure audit (in progress)

The audit intentionally starts with all merged passing receipts matching LPa–LPt, NBA–NBM and NP6, including candidates; this is a conservative superset of credited passes. `KDX_PASS_INVENTORY.json` records each exact receipt, command and source hashes. No new PASS receives bridge credit from this diagnostic.

## Execution accounting

Scopes: MemoryHigh=6G, MemoryMax=8G, MemorySwapMax=0, TasksMax=64, one at a time; existing S2H reservation and S2W runner unchanged. Admission requires exit0 AND allowed:true. No Lean: axioms N/A. No shipped repository file changes, so no ELF rebuild trigger. Inherited ELF pins are not newly reproduced.

Own-script corrections: setup transport initially exceeded the SSH argument limit before any launch; changed payload delivery to scp after admission. The replay extractor initially skipped helpers whose parameter types contained array semicolons, and missed function values passed to map; corrected extraction and added missing verbatim helpers. The original batch wrapper returned success after recovering failed receipts and failed to abort on compilation errors: corrected to stop when no harness is checked. KDX_K006–020 are **15 compile failures, zero verification results**, conservatively charged to the Kani budget. They neither pass nor refute their original credited harnesses. No timeout/memory-killed job has been rerun.
