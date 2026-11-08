# NNT staged composition

Prefix-only Lean modules and evidence. No shipped files or merged proof modules
are modified. The job-owned serial runner is adapted from NNS_run.py, retaining
its admission, disk, share, timeout, cgroup, transport and Lean settings. It now
pins every selected NNH_ object and sidecar before each launch in addition to
all resolved Aeneas library objects and direct imports. Cache seed is by
LEAN_PATH reference only; no cache or export is copied, moved or deleted.

L001 failed on an `open` syntax error (no timeout or memory kill); L002 corrects
that syntax. L003-L008 pass: domain-free canonical law membership, fallback,
full relational replay, native transport, literal stage2 parametric/weak/canonical
roots, and the exact installed r241 field. No new RowSpec/domain/trust premise.
