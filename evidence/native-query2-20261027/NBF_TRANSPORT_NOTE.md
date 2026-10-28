# Transport discipline note

All prover scopes are serial, each with its own admitted reservation and exact
caps. No scope was launched on allowed:false or a nonzero admission status.
A read-only host process/log observation and later read-only source-snapshot
archive overlapped an active launch SSH session. This departed from the
instruction to avoid extra parallel SSH sessions; it created no second scope,
resubmission, source mutation, ControlMaster or infrastructure change. All later
transport/recovery is serialized after the active launch completes.

## Redundant compile

NBF_L027 accidentally repeated successful NBF_L026's exact source/dependencies,
exit0,wall4.681775607s,RSS4418904KiB,swap0. This violates the unchanged-rerun
rule and receives no new proof credit. The own NBF_build.py validation now
rejects equal source hashes when every retained selected dependency hash still
matches. This is a stricter OWN runner check, not a shared launcher edit; the
inherited backend's lean-* glob did not cover NBF_L* names. No timeout or memory
kill was rerun, and no resource limit was raised.
