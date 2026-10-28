# Coherent closure rebuild and RunJoin continuation

Entry HEAD 9e389048b4a6587a74b52d5d4c70abad47cc6725, exact assigned worktree
/Users/dominic/ZK/.worktrees/pv-runjoin and branch codex/pv-runjoin-20261026.
Budget 100 Lean attempts, zero Kani; only IDs 51300–51499, audit IDs 51497–51499.
D330 authorization permits unchanged dependency modules in 20–40 module chunks,
one charged attempt and one capped scope per chunk. Proof candidates remain
one module per attempt. No old cache overwritten, no shared sources written.

The resolved union has 1983 project modules, no unpinned imports and no XR modules.
1982 dependency modules (excluding the endpoint audit itself) form 50 topological
chunks of at most40 modules. EJR/freeze precedence wins7 tracked-source conflicts;
both hashes are in build-plan.json. h5 modules are read from committed HEAD blobs.
The full source snapshot is focused-project-sources.json.xz with its uncompressed
SHA256 alongside. This is a new rebuild, not h6 reuse of stale project objects.
External objects are verified against the h4/SCOPE manifest before compilation.

Fresh host directory: codex-pv-runjoin-20261026/runjoin32-lean. LEAN_PATH contains
only its fresh project objects and manifest-pinned external objects. The old
runjoin24-lean directory and its provenance are retained. Existing host run2.py
is unchanged. Each chunk records per-module sources, dependency fingerprints,
object hashes, original compiler output hashes, exit, wall,RSS,swap and axioms;
the scope additionally records aggregate elapsed/maximum child RSS and swaps.
Every failed chunk stops at and identifies the failing module; no unchanged retry.

After rebuild: endpoint audit once; explicit LaneDenotation31 audit once;
NativeSnapshot31 preflight/audit once. Then V045 full native public/context/output
association using SnapshotAgreement31 and honest-family identification, followed
by V038 complete common-sample ROMView/observer agreement toward RustRealRefinement.
Neither snapshot equality nor passing audits alone discharges that refinement.
The trust list, observer, simulator, bad events, shipped Rust and ELFs stay frozen.
No new Kani credit is claimed; structural/native lane evidence retains its K-1
substitute class and finite native comparisons retain their finite classification.

A read-only ID-audit script initially mistook digit sequences inside hash columns
for sent.txt attempt IDs. The retained initial false-positive report is superseded
by parsing the actual third column; no compiler launched during either check.
