# ResourceActual bounded admission rehearsal

Read evidence/resource-actual-20261024/CRITERIA.md first. No compiler or consumer.
The operational gate and legacy helpers come unchanged from merged ResourceStat.
`ResourceActual_local.py tests` runs only own offline preflight and records a
receipt; historical suites are reused. `ResourceActual_audit.py` is the lead's
nonmutating offline source/hash/input/decision replay entrypoint after export.

Host operations are explicit, not default: `inspect` pins interpreter, stdlib,
mapped dependencies and external commands read-only; `stage` creates only the
assigned fresh private stage with read-only sources and manifest; `run` has an
exclusive local sentinel and a nonblocking established shared flock, exactly
one 4GiB prospective phase and at most one 3/4GiB scope with zero-additional GO;
`export` reads only own evidence. Neither denial path retries. GO precedes the
tiny in-process identity marker. Full ordered capture remains on host; large
ordered captures are exported in 1000-event shards. Oversized derived JSON
has a hash/size record plus bounded summary; no binaries are committed.

Do not rerun `run` or remove its sentinel. A future workload always needs new
lead authorization and fresh prospective/in-scope admission.
