# Transport discipline note

All prover scopes are serial, each with its own admitted reservation and exact
caps. No scope was launched on allowed:false or a nonzero admission status.
A read-only host process/log observation and later read-only source-snapshot
archive overlapped an active launch SSH session. This departed from the
instruction to avoid extra parallel SSH sessions; it created no second scope,
resubmission, source mutation, ControlMaster or infrastructure change. All later
transport/recovery is serialized after the active launch completes.
