# L188 audit plan

Authoritative roots: AspisR1.RPx_Deployed.deployed and AspisR1.JHx_Joint.source.
Read /Users/dominic/ZK/AGENTS.md in full and local-lean rules 1–15.
No existing proved module or frozen Rust will change. No Kani, no key cleanup.

Stages, each followed by a local commit:
1. Pin authority, roots, source/evidence census and cache-selection preflight.
2. One coherent final cached closure replay/audit, normal 6G/8G scope,
   swap 0, TasksMax 64, -M7000. Only an IMPORT failure permits the lead-approved
   single agg16 attempt after verifying all three runner hashes. No other
   unchanged failed replay is authorized. Budget at most six Lean compiles.
3. Release manifest, trust inventory, native coverage snapshot/deltas, checker,
   final validation and handoff. Open obligations remain visible.

Own cache /home/dombarker/project-offloads/codex-cx-l188-cache-20261028;
seed by copying selected objects from the pinned RPx and JHx search paths;
all predecessors remain read-only. Never delete own cache.
Admission requires allowed:true AND exit 0. One scope at a time.
Existing launchers only; infrastructure failures are a stop, own-input errors
are corrected with receipts. Reused objects are not a fresh library rebuild.
