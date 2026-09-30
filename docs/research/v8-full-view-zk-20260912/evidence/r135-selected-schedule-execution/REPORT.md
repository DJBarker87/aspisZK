# R135 verified evidence: explicit schedule execution

Date: 2026-09-30 (UTC)

`SelectedResearchScheduleExecution` exited 0 in 2.00 seconds, with peak RSS
3722676 KiB and swap 0 under the recorded 5G/7G `MemorySwapMax=0` runner.
All thirteen printed execution results use only `propext`,
`Classical.choice`, and `Quot.sound`.

The leaf constructs the schedule view from the already checked component
runs and proves `eval_run`; it does not define the run as `eval`.  The frozen
R117 selected callback remains pinned by its existing stage manifest and is
not modified by this proof milestone.

The source callback equality, source oracle distribution, privacy and
soundness remain open.
