# L187 coherent replay dry run

Pinned input revision: 7d1ea416bd4c185e63c278623727adc4f3c9c483.
Targets: AspisR1.FGl_Headline.deployed and AspisR1.Rc6_Top.deployed.
Budget: 400 Lean attempts, one module each; 0 Kani. No proof repairs.
Fresh workspace: /home/dombarker/project-offloads/codex-cx-replay-dry-20261026.

Replay begins with the complete dependency-order prefix, INCLUDING Lean's
Init dependencies; a partial replay must not silently exempt the compiler's
imported modules. Historical census graph is a planning input only. Source
imports and hashes are recorded for each attempted module. Fresh objects
are written only in the new workspace; no interim research objects are used.
Pinned compiler executable remains the bootstrap trust boundary.

Use unchanged S2W_run_host.py and S2H_reservation.py. Each module gets its own
6G high / 8G max / swap0 / tasks64 scope and -j1 -M7000. Admission retries
follow local-lean rules 6–7. Never rerun a failed module unchanged. Failure
blocks its dependent modules, not independent available work. No launcher
or monitor modifications are authorized.

The census contains 10,389 modules, more than the 400-attempt budget.
Consequently no complete closure or definitive whole-closure axiom result
can be promised in this run. All partial evidence will be labelled as such.

Before/after theorem statements: unchanged. Premises removed: zero; ledger
delta zero. No new non-vacuity claim. Historical FGl_Nonvacuity.composed is
not freshly certified until its own closure is replayed. No shipped source
changes; no ELF rebuild trigger. Target not yet established.
