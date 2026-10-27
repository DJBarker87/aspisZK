# Resume bounded Kani gates

No stubs; small-width control/indexing only. No SHA compression gate. All exact targets, source snapshots, revisions and cap records are in each collected-receipt.json.

| run | exit | wall | reported peak KiB | swap | verdict |
|---|---:|---|---:|---:|---|
| resume-string-path-01 | 0 | 0:01.48 | 181104 | 0 | PASS (bounded harness only) |
| resume-string-capacity-01 | 0 | 0:00.52 | 155092 | 0 | PASS (bounded harness only) |
| resume-join-one-byte-01 | 0 | 0:13.33 | 592468 | 0 | PASS (bounded harness only) |
| resume-string-push-r01 | 0 | 0:05.75 | 193752 | 0 | PASS (bounded harness only) |
| resume-pop-errors-r01 | 0 | 0:05.13 | 447524 | 0 | PASS (bounded harness only) |
| resume-array-exact-r01 | 124 | 3:00.00 | 15476 | 0 | TIMEOUT; no verdict; RSS excludes killed descendants |
| resume-array-reject-r01 | 0 | 0:05.97 | 459692 | 0 | PASS (bounded harness only) |
| resume-pop-single-r01 | 124 | 3:00.63 | 15652 | 0 | TIMEOUT; no verdict; RSS excludes killed descendants |

Charged 8/8. Six passes, two 180-second timeouts, no checked ROW counterexample. Timeout scopes checked absent; native/compiler/deployed associations remain explicit. #print axioms: N/A native runs. Prior ten-run budget is preserved in KANI-SUMMARY-prior.md.
