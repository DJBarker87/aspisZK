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

L009-L015 pass: L7's complete parse/resolved/stopped-arm proof, byte/header
transport and G1a field, actual-entry witness, and all four full top consumer
modules. L016 strengthens the interface's examples to direct old/new projection
rfl checks; no definition, field type or theorem statement changes. L017 is the
single passing combined import with NNN_COMBINED_IMPORT, NNS_ and all proof
modules. No unchanged regression is repeated. Type-only printing and raw audits
are separate evidence artifacts, not extra row credits.
