Actual extracted public serializer: successful-return composition, Lean 4.31

final-green contains three exact source files, their successful receipts/logs
and optional compiled objects. Successful checks were sequential:
  success-e: 22.445s, sampled group RSS2605504KiB, process swaps0;
  frontier-b: 17.718s, sampled group RSS2674912KiB, process swaps0;
  whole-d: 12.974s, sampled group RSS2770912KiB, process swaps0.
All 14 #print axioms outputs contain only propext, Classical.choice, Quot.sound
or subsets. No sorryAx/custom axiom occurs in the successful final audits.
Unused-simp warnings in success/frontier do not change the checked statements.

failed-attempts keeps success-a through d, frontier-a, whole-a through c,
including all receipts/logs and the three source snapshots actually retained.
Earlier source versions without snapshots are identified only by receipt hash.
Each failed due to a local proof/elaboration error, with no memory kill.
Error-recovery sorryAx in those logs is not a successful proof audit.

The fields proof directly unrolls the generated loop and uses remaining-list
length as its measure. frontier_eq_chain proves equality to all 20 generated
indexed calls. source_eq_program proves equality to the actual generated
public_bytes for both constructors; it uses cases and rfl. source_success then
proves exact literal tags and LE bytes plus canonical serialized words from
that generated function's successful-return premise. It has no capacity or
allocator-success premise. The finite chain/program is a proved factoring of
the generated definition, not an assumed handwritten Rust correspondence.

Prerequisite generated Types/Funs and helper evidence live in sibling bundles
named by pins.json. The exact retained backend source/object references still
match the helper bundle observations. This is not a backend/compiler replay or
proof of reproducible tool binaries. Source hashes and checkout_head identify
checked bytes; source_base_revision in the runner remains its older label.

The retained runner uses local absolute cache paths. Lean-M6000 and a sampled
7GiB process-group kill guard apply; this is not a systemd/cgroup limit.
No package-wide/cold build, build-host Lean, or unchanged green replay occurred.

The raw-carrier/byte mapping into Lean 4.32 PublicSourceRaw.serialize remains
OPEN. Tool extraction, standard-library model and actual runtime/allocation
trust boundaries remain. Zero withdrawal is still serializable; the separate
payment amount guard is not proved here. Full J1.a closure is not claimed.
