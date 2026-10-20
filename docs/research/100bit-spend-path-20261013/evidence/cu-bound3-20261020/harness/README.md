The analysis reuses the second-method CFG, longest-arm and residual algorithms.
Changes are address rebasing, source-cited adopted-format rules, explicit parent
SHA syscall residuals, provenance and duplicate-plan handling. No production
Rust/SBF code changes are required.

Host root H=/home/dombarker/project-offloads/codex-cx-cu-bound3-20261020.
The source archive is pinned by ../source-hashes.json; exact executed plans are
under ../plans. Build commands and all limits are in ../receipts. driver/ is the
exact native measurement crate input: place it at H/src/tools/r1-cost-probe-sweep;
clone to -sweep-trace and add trace=["litesvm/register-tracing"] to its features.
The component_checks.rs executable is copied to that crate's src/bin/.

build-sbf.sh rebuilds the Pool, verifier, profiling verifier and optional line
mapping ELF in separate capped scopes; build-driver.sh builds sweep/trace with
release -j 4. Native cc linking uses -Wl,--threads=4; SBF direct rust-lld uses
--threads=4. The deployed and linked pins must match before replaying controls.
make_plans2.py emits only the nonempty accepted split-10 domain. The actual
random plan was split into independent random-a/random-b outputs; plans include
the two split11 rejection counterexamples and six fresh-public-equality controls.

Every heavy command uses systemd-run --user --scope -p MemoryHigh=6G
-p MemoryMax=8G -p MemorySwapMax=0 -p TasksMax=64. reservation.py records the
sum of populated reservations (55 GiB maximum). sweep.py records one receipt
per native execution, resumes completed labels and retains all task key files.

run_audit.sh creates stage1/stage2/pool JSON from exact-proof register replays.
analyze.sh regenerates rules, maps byte-matched source lines, classifies residuals,
checks hash counts, attributes profiling variation and computes B. Pool line
maps and old verifier linked ELF are reused from the pinned second-method host
workspace; no old site classification is substituted for the new verifier.
After the sweep completes, rerun only bound2.py to incorporate its final rows,
then make_deliverables.py and check_results.py. finalize.py retains INCOMPLETE
for the literal two-accepted-split request even though all inequalities pass.
cleanup_traces.py hashes then removes only this task's .regs/.insns files.

Fresh OS masks are intentionally not reproducible from a public seed. Exact
trace replays used retained host proof/public sidecars; no private key or
mask secret is exported to this evidence directory.
