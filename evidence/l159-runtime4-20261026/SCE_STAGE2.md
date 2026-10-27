# Stage 2: actual adaptive chronology separated from projection

SCE_Execution.accepted_eval computes the full response-driven account execution
in exact order: prefix, TX1 wrapper, second choice, TX2 wrapper. It assumes only
the successful FIRST SOURCE wrapper evaluation needed to reach the second
choice, not an unrelated native execution or caller-chosen log.

SCE_AdaptivePadding.pad inserts one allowed oracle call into the second choice.
Its second submitted value is unchanged, as are the COMPLETE terminal outcome
and first ByteProver. log_length proves the account issued log grows by one.
This is not an accepted-source fixture or a deployed attack; it demonstrates
why the chosen first-only P misses adaptive work. A complete-account P is being
checked separately, with its full query charge retained.

SCE_Physical.run_eq_iff proves the exact remaining log and acceptance clauses
after the input projection. chronological_iff exposes the needed account-log
versus prefix-plus-fixed-pair-source log equation. Neither is adopted as trust.
No SCE_Physical.run_eq or SCE_Top.deployed is claimed at this stage.

Attempts004–006 pass with standard axioms. All input declarations remain honest;
no removed top premise is claimed. Attempt004's configured source_revision is
the PREPARED anchor 9d2399d9b59ea13903a72ff9afddb177dcaacfab plus exact dirty
source snapshots; actual local launch HEAD was580205338a. This metadata
correction does not change its exact source/object hashes. Attempts005/006
use580205338a explicitly. No source, toolchain or artifact adoption occurred.
