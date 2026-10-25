# Frozen target and validation scope

Source baseline: `30c4fd3eba3bdad6ea5cab8152abe14a4c21a234`, branch `codex/cx-native-p6-20261026`. `NP6_start.json` records exact shipped Claims, wire, heap, original top and ledger hashes. `NP6_check.py` reconfirms them against this worktree. No shipped source, protocol parameter, feature selection, wire shape, acceptance criterion, failure event, security metric, key or wallet changed. Proof candidates stay in NP6_ modules and evidence only.

The copied proof crate uses `aspis-core`'s r0 feature and private-leaf-salts default; prover/r1p-check are disabled. Cargo manifest and source hashes are in every accepted receipt; the retained resolved lock is `NP6_claims/NP6_Cargo.lock` (evidence copy, not an installed workspace lock). Claims-specific behavior is the same literal source under these features. The canonical wire row25 shape remains5+116*32 bytes. The full parser fixture is13831 bytes. No valid-byte or success assumption narrows the arbitrary Kani contents.

Kani0.67.0, Rust sysroot nightly-2025-11-21, CBMC6.8.0, solver cadical for accepted gates. Compiler/driver/CBMC/goto-instrument hashes are in `NP6_tools.txt`. Rust verification uses opt-level3, four build jobs and default safety/overflow/bounds checks, explicit per-loop unwind32 with unwinding assertions. Object-bits16 and dereference caching control representation, not adversarial byte values. `--no-assertion-reach-checks` disables only extra reachability checking of assertions. The accepted construction gate has explicit reachable success/error covers; real native fixture and constructor witnesses supply separate non-vacuity. There is no stub or assumption of successful decoding.

Lean4.32.0, binary hash `e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550`, `lake env lean -j1 -M7000 -DElab.async=false`. All18 new NP6 modules compile in focused targets; every new top theorem prints its axioms. Only propext/Classical.choice/Quot.sound or none occur in successful checks. One final focused cached closure audit L029 was run, not a package or frozen-manifest replay. Failed elaborations and any sorryAx in their diagnostics are excluded.

All host jobs ran individually in systemd scopes: MemoryHigh6G, MemoryMax8G, MemorySwapMax0, TasksMax64. No cap was raised. The unchanged existing S2W Lean launcher and an unchanged prefix-named copy of its Rust launcher were used. Coherent SInt2 objects were reused. The final audit/cleanup preflight had only init.scope running (one8GiB reservation; host safe limit55GiB). Per-attempt limits, cgroup, peak, RSS, swap, exact command, target, dirty source snapshots and dependency hashes are retained. There were no missing dependency builds, OOM kills or unchanged retries. Whole-body attempts that timed out or grew near6.4GiB were split into different finite properties before further runs.

For K003/K007-K009/K016, GNU time reports the timeout parent's RSS (~15MiB), not aggregate CBMC child RSS. Those failed attempts are NOT successful resource evidence; use their cgroup peak and raw logs. Manual CBMC growth stops K001/K002/K010/K012 record observed child RSS near6.4GiB. No checked shipped-source counterexample was found. K027/K028 fail because custom GlobalAlloc dispatch is absent in that Kani profile; diagnostics remain excluded. Optional uninit instrumentation K005 failed in the compiler and is not claimed.

Early configs reused their initial source_revision label. `NP6_launch_revisions.json` separately records actual branch HEAD for each launch without rewriting raw receipts. Exact dirty source snapshots/hashes identify what each checker consumed; shipped source hashes were unchanged throughout. The final source proof and accepted theorem launches used c55953b810 plus those recorded dirty NP6 sources.

The inherited SInt2 `object-source-manifest.json` / `final-closure-manifest.json` pin the selected extraction/cache closure. `NP6_extraction_origin/` copies the original run10 Charon/Aeneas input/receipt/source pins as provenance, not a new extraction. Its historical caps/times are not counted as new jobs. This delivery does not rebuild the extraction/compiler or represent cached object hashes as identical to other historical variants.

No cfg(kani) harness was added under crates/ or programs/, so the conditional ELF rebuild requirement was not triggered. No SBF build was launched. These ELF pins are INHERITED, NOT freshly reproduced:

- default `f8c0ec72621fd5029a97d796c4a3623d0dc44a8e7074122372f9872915d143d4`
- devnet `63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299`
- Pool `121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548`

This is local source-refinement evidence under the existing trust boundary. It is not a new frozen-release result and supplies no attack-work/security number.
