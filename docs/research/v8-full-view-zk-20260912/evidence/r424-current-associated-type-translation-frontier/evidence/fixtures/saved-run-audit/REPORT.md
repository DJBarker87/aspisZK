# R424 fixture build and execution audit

Saved receipt/source/metric checks: PASS.

Three build attempts are retained. v1 failed at `TraitImplId.Map.find_exn`; v2 failed on the associated-item map type annotation; v3 built the dedicated `ConcreteAssociatedTypesFixture.exe` target successfully. The v3 target/source revision and all five source/input hashes match the saved input manifest and snapshots.

- v1: exit 1, 1:25.40, 590,092 KiB RSS, 0 swaps.
- v2: exit 1, 0.66 s, 211,416 KiB RSS, 0 swaps.
- v3: exit 0, 1.34 s, 254,976 KiB RSS, 0 swaps.

The saved execution command used executable SHA256 `a8f7fec43708590d256b7a4f313bb63814f9075deb77ef064768ba13318c055f` with exact R396 input SHA256 `399020435e94aaa7135c06d68445e9b936bd22fe6d1e1d197ee708d448d584ae`. It exited 0 in 0.08 s at 42,944 KiB RSS with zero swaps; the raw output reports all 14 assertions passed. The command/receipt source hashes agree with the successful v3 build inputs. The execution receipt records the 5G/7G/zero-swap/128-task limits, and the launch transcript names the systemd unit; there is no separate cgroup-property snapshot for that execution scope.

The original v1/v2/v3 metrics receipts are preserved byte-for-byte under `build-preflight/history/fixture-boundary-correction-v1/`; their stale boundary strings claimed assertion success during build phases. Current metrics receipts now state phase-correct boundaries. The v1 and v2 failure logs remain unchanged, and the separate execution log is the sole 14-assertion result. Fixture source revisions are archived: `reviewed.ml` is v1 (Map API failure), `reviewed-v2.ml` is v2 (type annotation failure), and `reviewed-v3.ml` is the exact successful v3 source.

This establishes only a finite fixture build and one execution against the frozen LLBC. It does not establish universal binder/GAT correctness, compiler/source correspondence, actual callback execution, translation success, Lean theorems, or security.
