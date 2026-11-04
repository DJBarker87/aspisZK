# D586 — READY-TIMING (prepared only)

Worktree `/Users/dominic/ZK/.worktrees/pv-uc`, branch `codex/pv-uc-20261029`, base/source acceptance revision `a0a1bafab22a11f3be4a26560736feade8aebfe0`.

The local and host `final-gates/ready/build.json` now bind user_client SHA256 `fc8808eb454f3156dba550140398cc3a74af4c88ee5b3491d2d04d33ee904558`, 2,031,048 bytes. The previous uc4 packet is preserved as `previous-ready-build.json`. The replacement reuses uc5 `final-build.json`, N91108 receipt, original launch revision `0f8f8f282050ca0ab0e5ec7ba6216875835eaf6c`, staged input record and recipe, each hash-linked in provenance. The later a0a1bafab2 revision accepts the final evidence; it is not misrepresented as the build launch revision. Every client source hash matches both N91108 inputs and a0a1bafab2. No compilation or rebuild occurred.

Host check-ready.py executed only the five selected runner AST statements (binary paths, expected pin, three assertions). Baseline `30d883a8d97f12c315898aaf9170eb7a542b5e935881f089506fd4601ddb6a20` and draft fc8808eb pass; the packet also must explicitly pin fc8808eb. No runner main body was imported/executed. `hash-check.json` records executable sizes/hashes and runner/packet hashes.

All 18 offline tests PASS on host and Mac: the original 17 guard tests, updated authorized IDs, plus synthetic uc5 raw output-pipe wiring/record equality/FD closure. The runner now supplies the required distinct wallet_output_fd and validates the fixed 212-byte record in memory, following uc5's completed differential harness. No custody bytes are written to evidence. This is synthetic wiring evidence, not a new real-client differential. Prior 100-pair evidence is reused. Process wall timing includes pipe retrieval/validation; prove_wall_seconds is unchanged.

The own launcher is copied from scope901.py with only evidence destination, stage manifest and ID/budget range adjusted. Guard/barrier accept only N91120–N91125 with unchanged 6G/8G/swap0/Tasks64, named live window, admission and continuous foreign-scope rules. N91120 is absent locally and on the host. No native scope was consumed. No shared marker, reservation tool, production source, keys or balances were changed. The inherited prompt-pv-uc.txt referenced by uc3 was unavailable; supplied task scope and available chain were followed.

Receipts: `receipt.json`, GNU time logs, `offline-tests.txt`, `source-provenance-check.json`, `host-staged-hashes.txt`. Modified tooling hashes accompany the base revision; all staged host files equal local reviewed files. Zero Lean, client executions, timing samples, rebuilds and capped scopes. No privacy endpoint premise removed/added/weakened; privacy target remains unestablished.

The lead arranges a live `for = pv-uc-timing` window and runs exactly:

```sh
python3 /Users/dominic/ZK/.worktrees/pv-uc/tools/pv-uc6-20261104/scope.py native91120 d561-timing python3 /home/dombarker/project-offloads/codex-pv-uc-20261029/timing-window.py
```

This command was NOT executed. The historical phase/output directory name d561 is retained for compatibility. No timing verdict is claimed. Local commit only; no push or merge.
