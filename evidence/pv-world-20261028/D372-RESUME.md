# D372 resume

Start: 95740e686418809a3ceade00cf558cd5a42cc180, same worktree and branch.
Fresh budget 100 Lean compiler starts, zero Kani, IDs 50400–50499 only;
50497–50499 reserved for audits. Previous run's compiled-artifact cleanup
removed the private cache: dependency recompilation restores missing artifacts,
not an unchanged regression. External h4 objects freshly revalidated before
any compiler start; shared sources and external objects remain read-only.

Exact scoped fxmem sources are imported from the candidate's merge 46a2203505,
with per-file origin pins in d372-fxmem-source-pins.json. The frozen extraction
is byte-identical across that source cohort and this worktree. These are
source packages; raw primitive realization and deployment are not silently
assumed. No merge, branch switch, source change under crates/programs, T field,
key operation, or ledger/endpoint change is authorized or performed here.

Per-attempt upload and admission inventories remain on the host. Local evidence
retains the decision, path and exact-byte SHA-256. This avoids repeating large
object/cgroup manifests per attempt. Resource caps remain 6G/8G/swap 0,
TasksMax=64, Lean -M7000, one scope at a time.
