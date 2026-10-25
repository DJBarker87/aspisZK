# Fixed Linux 4.32 workspace preparation proposal

For lead review only. No installation, artifact transfer, build, Lean invocation,
new remote query, shared workspace adoption or runtime admission is authorized by
this proposal. The standard fixed 4.32 root exists, so an installation proposal is
not needed on these data.

Use the literal `/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0`
only as the candidate toolchain root for a separately allocated Linux workspace.
`observation-summary.json` supplies the finite 14-file hash/size catalog and five
ELF header observations from this action. Retain these exact hashes as candidate
inputs; do not select 4.31/4.33 from the shallow names or infer provenance from the
4.32 directory label. The five ELF headers are class 2, little-endian, machine 62.
The runtime interpreter, native initializers, loaders and full dependency bytes
remain unpinned and unexecuted. Header observations do not establish ABI closure.

Next concrete deliverable is a lead-allocated fixed Linux 4.32 workspace/runtime/
ABI/artifact catalog plan: exact new private workspace path, approved released
source-input manifest, explicit executable/runtime/dependency file allowlist and
hash receipts, and the exact catalog consumer/admission target. This should avoid
all other live workspaces/caches and preserve existing jobs. The historical
`run-joint.sh` and `lean-toolchain` literal paths returned ENOENT; do not adopt,
execute, relocate or discover a replacement launcher. The historical sources path
exists as group-writable directory metadata only; no entries were read or adopted.

Local Darwin arm64 versus remote Linux x86_64 is an explicit architecture boundary.
Do not transfer or adopt local serialized artifacts on the strength of version
labels, source-text hashes, or these five ELF headers. Full 9080-core/Core6060,
actual serialization compatibility, complete caller/kernel/axioms/refinement,
SDK/runtime/extraction/native/artifact/security joins remain open.

Before any later generated certificate aggregation, obtain fresh aggregate
populated reservations below 55 GiB with the required reserve 7 GiB, guard 2 GiB
and visibility assessment; current runtime/catalog/caller admission remains open.
Use an independent MemoryHigh=6G, MemoryMax=8G, MemorySwapMax=0, TasksMax=64 scope,
or an existing stricter 5G/7G scope without raising it. Parallel Lean only in
22:30–14:00 Europe/London; otherwise use the shared global lock. No reservation
check, lock claim or capacity GO was attempted in this metadata action.

Soundness 367/368, Kani 59/60 and private budgets are unchanged. Both security
targets remain NOT ESTABLISHED. Stop here for lead review.
