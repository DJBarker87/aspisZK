# Relaunch accounting

At start of relaunch 2, prior WIP 0cdb792b74 and host directory contained no compiler/native receipts or objects for this task: 0/100 Lean, 0/60 native, 0 Kani consumed.
62500 elaborated inherited Link but failed writing object because own output directory R1Z had not been created. Charged; no object credit. Created own output directory and retried unchanged source with changed environment as 62501: passed. No infrastructure changes.
The inherited id-preflight.json was accidentally run locally (directories_scanned=0, Mac RSS units); it was insufficient cross-job evidence. Supplemental id-host-scan.json was run on host after 62501 and scanned 60,732 directories and shared sent files; no other-job collisions. No claim the earlier scan was adequate.
62530 was refused by the in-scope barrier before Lean (59,995,324,416 reserved > 59,055,800,320 safe bytes at 00:24:22 UTC). No compiler start charged. Retry only after 00:27:22 UTC, same ID per m'.
The task wrapper now explicitly checks allowed:true from the same-shell launch admission JSON as well as its exit status, and retains that admission. Earlier launch admissions are recovered and audited rather than inferred from the initial snapshots.
