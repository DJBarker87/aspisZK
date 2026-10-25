# Source022 handoff — STOP for lead review

Branch `codex/cx-prover-rw-20261023`; immutable first candidate `018e9d2aff669c3b1292e3ad49dfdc9a7d605620`. Preservation stage `6ba7932d0a`; corrected source stage `4e5732ddd47429677d6d068625d3286f608f64fe`. No merge or push. Corrected v6 is prospective and remote-unobserved; it supersedes the first candidate for future review, never its historical byte identity. Full lead v6 source review remains incomplete; no accepted release or actual v6 allocation is claimed.

## Exact repair and scope

Before: `Proc.cancel` returned `verified-disappeared` after independently verified pidfd-open disappearance or optional identity absence; cleanup accepted only `('disappeared', 'verified-owned-signalled')`. Verified Gone from pidfd-signal escaped as a cancellation error.

After: those two verified absence paths return the original public `disappeared`; pidfd-signal also maps only `Gone` to `disappeared`, inside the existing descriptor-closing `finally`. Detailed verification remains in `proc_events`. Cleanup's acceptance tuple, Guard.cancel_owned, all other guard methods, independent absence tests, identity envelopes, readiness, ownership, policies and controls are unchanged. Permission, live/unknown visibility, reuse and uncertain control still fail closed. This establishes source-level compatibility for these concrete mocked producer/guard/consumer paths, not actual termination or native control.

Complete before/after Proc, Guard, cancellation and consumer definitions: `complete-producer-guard-consumer-functions.json`; all maintained changes: `source-diff.txt`. Metadata-only source refresh/builder changes identify source022 and repin the exact corrected overlay. No crates/programs/shipped protocol/wire/feature/security-contract change. No formal statement or premise change; no assumptions discharged or added. Installed OS/CPython/no-untrusted-writer trust remains.

## New and reused evidence

The archived first candidate fails the new concrete already-gone join test exactly as reported by the lead; `v6-counterexample-022` retains failure, original source pins and log. Lead counterexample and Mac fixture preflight failure are copied unchanged. Linux-only pidfd APIs use mock `create=True`; no actual PID signals/syscalls/host action.

New: eight concrete Proc -> Guard.cancel_owned -> actual Guard.finish -> cleanup tests; one existing affected cancellation test; ten affected lifecycle/order/persistent-thread bridge tests; one focused source/pins/import audit and byte-identical fresh reproduction. All replacement tests and audit PASS. Caller clone changes PINS only; complete remaining AST equals source021, including disabled main and capture/runtime paths. Its new pin validation ran locally. Source021's original caller and all its evidence remain unchanged.

Reused: remaining source021 guard/caller fixtures and release receiver tests only for unchanged functions, under exact byte/AST assessment; old 33+21 suites were not rerun or represented as new validation. Fresh changed closure checks all current source/bootstrap/plan/seals, exact payload coverage, fixed stage, four disabled maintained mains, two SETUP overlay mains only, two disabled final mains and seven null fields. First candidate's 141 source/release files (2,306,323 bytes) were archived before edits/rebuild, plus original caller/pin records. Old v1-v5 and historical evidence are unchanged by git path audit; no large historical inventory replay.

Each receipt contains exact argv/exit/wall/RSS/swap/revision/source dependencies/runtime/interpreter hashes and N/A axioms; `validation-input-bindings.json` additionally pins reused runner/test inputs and archived counterexample inputs. Existing bounded runner reused; no new launcher/framework. Limits were sampled self+child512MiB/deadline30s, not a continuous physical-memory theorem. `commit-binding.json` connects tested source hashes to the committed corrected bytes; no unchanged regression was repeated.

| Target | Exit | Wall s | Child peak RSS bytes | Swap |
|---|---:|---:|---:|---:|
| v6-cancel-predecessor-022 | 0 | 0.129494 | 30736384 | 0 |
| v6-counterexample-022 | 1 | 0.222657 | 29491200 | 0 |
| v6-join-022 | 0 | 0.142191 | 31096832 | 0 |
| v6-lifecycle-bridge-022 | 0 | 0.123363 | 34717696 | 0 |
| v6-rebuild-022 | 0 | 1.123639 | 43991040 | 0 |
| v6-source-audit-022 | 0 | 2.854344 | 107134976 | 0 |

## Old first-v6 / corrected prospective pins

| Pin | First v6 | Source022 |
|---|---|---|
| Receiver SHA256 | 1c7a2f8186f8ccd4058038432c60a3d688e346b01fff3941694c931a461c480e | 5252c1bcc64729df99d8dd6b2f6784315f26a851ea298098c5eb1a3ae3a1a825 |
| Transport SHA256 | 7ad8fee820bf1d3a4211c98f0550cd21d461cec7613ecea639317457037461c5 | c0b89877d390bd3a7ca6fd134df98f165bab22d9a90ff3af3dd00d270c693c60 |
| Transfer root | 5cbeb415a6aa21a15137de557d3ca700f51b46fe2eb779aef07e75c606d5d927 | 7e95f639f0f7a34e3d0393bf6f3e6e3b23350779dc5b1ec3fb6ec0568e52ee73 |

Receiver size 883889; transport size 3854; payload 68 files / 691075 bytes. Exact leaf `/home/dombarker/final-native-gate-v6-20261025`; existence UNKNOWN, reject ANY preexisting entry. Old/current complete pins retained in archive, `v6-exact-pins.json`, `audit-result.json` and reproduction manifest.

## Remaining blocker / next deliverable

STOP for lead source/transport/pin review before ANY execution. No staging/upload/query/setup/SSH/native/compiler/Lean/Kani/RPC/key/root/config/permission action occurred. Port36 cold stat PID20432 and LaunchHistory18652 were not accessed. No allocation or reserved budget consumed/changed. Full55/reserve7/guard2/fullrootresidual/rawvisibility/both scans/own cap once/prospective1G/actual768MiBHigh1GiBMaxSwap0Tasks64/inside-controls-before-acquisition/full-GO+stability remain unchanged. Kani59/60 and soundness367/368 remain RESERVED.

Current manager default/devnet/Pool ELF pins unchanged; no new identity gate. All SDK/std/runtime/extraction/sourceDrop/native/artifact/security joins remain OPEN, including unresolved kernel/D-state control boundaries. Both security targets remain NOT ESTABLISHED. Next deliverable is lead review of source022; any future action requires a separate allocation. No owner question.
