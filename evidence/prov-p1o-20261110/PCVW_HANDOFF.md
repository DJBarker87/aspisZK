# PCVW_ HANDOFF: phase P1o (jobs-identity check and warm-build attempt)

Target not yet established. Frozen 4bb3b3f, original Aeneas 959659a6 (sha verified), nothing pushed, no sorry, no Lean scopes.

Scopes: W001 warm (statement chain, jobs 1, 900 s) exit 0 in 337 s, peak RSS 851 MB; E001 credited identity rerun of PCVT_E014 at 1/1, exit 124 at 180 s; E002 cost-probe items (jobs 1), exit 124 at 180 s. Caps 3G/4G swap 0 unraised.

Finding about the warm-build class: W001 and E001 had identical Charon command, env, cwd, dest-file and cargo settings, yet the workspace-crate unit directories got new metadata hashes in E001 (fingerprint JSON contents equal) and were rebuilt; only third-party units are reused (PCVW_CLASSIFICATIONS C3). The class cannot warm the workspace crates that dominate the time. Identity check stopped; verdict NOT_ESTABLISHED (PCVW_JOBS_IDENTITY.json, with the tag list of 28 non-pinned specs). Three cost-probe items FAILED (exit 124). Negative control not run.

Next: a longer-wall way to run Charon (or an owner-approved timeout), or identify the per-run input that changes the workspace unit hash.
