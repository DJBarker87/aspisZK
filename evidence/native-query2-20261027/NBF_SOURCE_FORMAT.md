# Scratch harness source format

NBF_harness.patch is the latest aggregate patch against frozen Rust revision
4bb3b3f51e16b4525f1d10336e2b0bcbbd775387. Each NBF_Kxxx directory retains
its exact historical NBF_harness.patch and source hashes. The source snapshots
were recovered before own Rust target cleanup. No .rs harness is installed
in repository crates/ or programs/.

NBF_payloads.py reconstructs the two added harness payloads directly from the
aggregate patch. NBF_sync.py and NBF_run.py use this reader. The terminal
static audit checks payload hashes against the terminal scratch source.
Earlier incremental generator scripts are historical authoring recipes, not
reproduction entry points for all30 independent snapshots. Reconstruct the
specific run patch to reproduce that run. Budget is exhausted; these scripts
do not confer permission to launch new runs.

A declaration in the aggregate patch does not establish a pass. Consult
NBF_HARNESS_STATUS.json, individual run receipts, and NBF_query_BRIDGE.md for
exact domains, stubs, exclusions and OPEN associations.
