# Snapshot timing deviation and hash-checked recovery

The initial resume5 client escaped shell double quotes into literal filename
characters. Its `test -f` therefore did not recognize pre-existing paths, and
the intended pre-replacement source/object copies were not made. This is a
procedural deviation from the shared-source snapshot rule. It is not described
as a pre-run snapshot after the fact.

The preflight inventory records the original source and object hashes before
all rebuilds. Among completed original-92 targets, exactly seven source/object
pairs existed initially. All seven original source hashes match the retained
repository bytes, and all seven original object hashes match the current object
bytes. `resume5-snapshot-recovery.json` records every result. Those exact bytes
were copied into the job's `snapshots/resume5-recovered/` after the error was
found. No pre-existing byte content was lost or changed in those seven pairs.
Other original-92 targets had no pre-existing source or object at preflight.

The shell grouping is corrected before the two differently sourced extraction
modules are rebuilt. Future copies use actual double-quote grouping around
`$p`, and remain under the assigned job directory. No launcher, environment,
memory cap, existing proof source in this worktree, or foreign worktree changed.
