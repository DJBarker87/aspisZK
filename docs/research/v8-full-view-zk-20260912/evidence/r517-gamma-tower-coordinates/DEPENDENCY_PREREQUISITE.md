# R517 unchanged tower dependency prerequisite

The first bridge attempt, `aspis-focus-1791053770900814000`, stopped because
the pinned cache lacked
`AspisV8R17/QuadraticTowerOperations.olean`. That was an environment-cache
absence, not a theorem failure or source change.

The exact existing source was copied without edits from:

```
docs/research/v8-full-view-zk-20260912/lean/AspisV8R17/QuadraticTowerOperations.lean
SHA-256 48fe57215f6f386dd5101d4006f8d31969efebe5a6505eeda19c03b0589d8192
```

Focused prerequisite `aspis-focus-1791053786305358000` compiled that unchanged
module under the pinned 5G/7G/no-swap/TasksMax128 configuration, exit 0, wall
0:01.00, RSS 1,192,084 KiB, swap 0. Its source snapshot, complete axiom log,
and receipt are retained in `focus-records/`.
