# LOG D354: independent KMX replay

In progress. Target not yet established. Base `6d4350e42c6181924b80483f19fa6ccac5c3b4a7`, branch `codex/pv-kstub-20261028`, fixed worktree `/Users/dominic/ZK/.worktrees/pv-relink`.

Read pv-common through (r'), including (r) and (k'), restored-host flag, root security/proof discipline and companion rules. No crates/ or programs/ change is authorized. Budget 30 Kani runs and 10 Lean attempts; Lean IDs44700–44799 only.

Exact research KMX patch SHA256: `bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67`. Research input snapshot `14e775c74a8ff9acb39a9b327ca18172d7ccde43`; the scan and row consequences are retained here. No self-written copy replacement.

13 historical exposed roots require paired replay (V178:4, V179:3, V182:3, V195:2, V233:1). V233 is split into two length windows retaining arbitrary output coordinates, for 14 pairs / 28 planned runs. Two runs remain for changed-timeout or corrected-input attempts. Large-window results require the Lean frame/coverage check before credit. Host scope caps6G/8G/swap0/tasks64, one scope at a time, CPU0–3, optimized Cargo, unwinding assertions enabled. A timeout gives no credit. A false postcondition after each original complete property is the negative control; only its explicit assertion failure counts.

Initial upload admission at 04:35:07 UTC refused aggregate reservation; no compiler or solver started. Waiting three minutes before retry.
