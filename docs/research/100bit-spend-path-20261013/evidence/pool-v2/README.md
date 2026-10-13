# Pool adapter v2 LiteSVM runs

These records use the root-audited v2 adapter ELF (`c73cfb72515dfd8de491a272999c7a64a2e751f60491da50f952faac4f031d6e`) and the optimized `pool_gate` driver built from fix3. Each run has a JSON evidence file, recorder receipt, and captured log. The run receipts record the 4 GiB `MemoryHigh`, 6 GiB `MemoryMax`, and zero-swap scopes. No task key files are copied here; the harness-created retained keys remain in their per-run task directories on NUC.

| Case | Outcome | Stage 1 CU | Terminal CU | Replay CU | Stage 1 / terminal tx bytes | State check |
| --- | --- | ---: | ---: | ---: | ---: | --- |
| transfer success, blockhash-fix rerun | accepted | 1,342,257 | 1,374,214 | — | 262 / 845 | settlement checks passed |
| withdrawal success | accepted | 1,340,896 | 1,390,507 | — | 262 / 1,010 | settlement checks passed |
| transfer proof rejection | rejected | 1,342,257 | 173,960 | — | 262 / 845 | byte-exact rollback |
| transfer wrong release | rejected | 1,342,257 | 38,129 | — | 262 / 845 | byte-exact rollback |
| transfer stale lane | rejected | 1,342,257 | 75,068 | — | 262 / 845 | byte-exact rollback |
| transfer replay | accepted, then replay rejected | 1,342,257 | 1,374,214 | 23,727 | 262 / 845 | replay preserved settled state |
| withdrawal proof rejection | rejected | 1,340,896 | 186,190 | — | 262 / 1,010 | byte-exact rollback |
| withdrawal wrong release | rejected | 1,340,896 | 50,578 | — | 262 / 1,010 | byte-exact rollback |
| withdrawal stale lane | rejected | 1,340,896 | 87,312 | — | 262 / 1,010 | byte-exact rollback |
| withdrawal replay | accepted, then replay rejected | 1,340,896 | 1,390,507 | 26,574 | 262 / 1,010 | replay preserved settled state |

Each case reused its matching v1 proof and public sidecars. The uploader made 137 proof writes and 3 public writes in 900-byte chunks: 140 uploads, 170,859 serialized write-transaction bytes, and 172,161 bytes across init/write/finalize transactions. The largest lifecycle transaction used 749,057 CU. The source also verifies that repeat-init and repeat-finalize reach the program and fail with nonzero CU after expiring the blockhash.

Both replay runs expired the blockhash before the replay transaction. The replay reached the Pool program (23,727 CU transfer; 26,574 CU withdrawal) and returned custom error `0x41532026`, which the pinned Pool source names `NullifierAlreadyConsumed`; it was not a duplicate-transaction `AlreadyProcessed` result.

This is deterministic local LiteSVM and compute evidence for the unproved cost-probe route. It does not establish protocol security or close a cryptographic proof obligation.

## Pair-255 edge gate

The updated driver accepted `--pairs 255` and generated fresh transfer proof/public sidecars for the root-history rollover boundary. The transfer terminal did not complete under the 1.4M limit: adapter stage 2 entered the verifier, which consumed 1,287,337 of 1,287,393 remaining CUs and failed its meter; Pool had consumed 1,399,944 of 1,400,000 CUs. The run receipt and full failure log are retained as `pool-transfer-pairs255-v2-run.json` and `.log`. No withdrawal pair-255 or CPI-negative run followed this unexpected cost failure. The generated task directory and keys remain on NUC.
